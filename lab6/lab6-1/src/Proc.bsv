import Types::*;
import ProcTypes::*;
import CMemTypes::*;
import MemInit::*;
import RFile::*;
import IMemory::*;
import DMemory::*;
import Decode::*;
import Exec::*;
import CsrFile::*;
import Fifo::*;
import Scoreboard::*;
import GetPut::*;
import Ehr::*;

typedef struct {
  Instruction inst;
  Addr pc;
  Addr ppc;
  Bool epoch;
} Fetch2Decode deriving(Bits, Eq);

typedef struct {
  DecodedInst dInst;
  Addr pc;
  Addr ppc;
  Bool epoch;
  Data rVal1;
  Data rVal2;
  Data csrVal;
} Decode2Execute deriving(Bits, Eq);

typedef struct {
  ExecInst eInst;
  Addr pc;
  Addr ppc;
  Bool epoch;

} Execute2Memory deriving(Bits, Eq);

typedef struct {
  ExecInst eInst;
  Addr pc;
  Addr ppc;
  Bool epoch;
} Memory2Writeback deriving(Bits, Eq);


(*synthesize*)
module mkProc(Proc);
  Ehr#(2, Addr)    pc  <- mkEhrU;
  RFile         rf  <- mkBypassRFile;  // Refer to p.20, M10
  //RFile         rf  <- mkRFile;
  IMemory     iMem  <- mkIMemory;
  DMemory     dMem  <- mkDMemory;
  CsrFile     csrf <- mkCsrFile;
  
  // Control hazard handling Elements : 2 Epoch registers and one BypassFifo
  //Reg#(Bool) fEpoch <- mkRegU;
  //Reg#(Bool) eEpoch <- mkRegU;
  Reg#(Bool) epoch <- mkRegU;
  Fifo#(1, Addr) execRedirect <- mkBypassFifo; 
  
  // Fetch stage -> Rest stage PipelineFifo
  Fifo#(1, Fetch2Decode)  f2d <- mkPipelineFifo;
  Fifo#(1, Decode2Execute)  d2e <- mkPipelineFifo;
  Fifo#(1, Execute2Memory)  e2m <- mkPipelineFifo;
  Fifo#(1, Memory2Writeback)  m2w <- mkPipelineFifo;

  // Scoreboard declaration. Use this module to deal with the data hazard problem. Refer to scoreboard.bsv in common-lib directory 
  Scoreboard#(4) sb <- mkPipelineScoreboard;


/* TODO: Lab 6-1: Implement a 5-stage pipelined processor using given a scoreboard. 
   Scoreboard is already implemented. Refer to common-lib/scoreboard.bsv and PPT materials. 
   Use the interface of the scoreboard.bsv properly */
  rule doFetch(csrf.started);
    let inst = iMem.req(pc[1]);
    let ppcF = pc[1] + 4;
    //if(fEpoch != eEpoch) begin
	//fEpoch <= !fEpoch;
	//pc[1] <= execRedirect.first;
	//execRedirect.deq;
    //end

    //else begin
	//let inst = iMem.req(pc[1]);
        //let ppcF = pc[1] + 4;
	//pc[1] <= ppcF;
	//f2d.enq(Fetch2Decode{inst:inst, pc:pc[1], ppc:ppcF, epoch:fEpoch});
    //end

    /*if(execRedirect.notEmpty) begin
      execRedirect.deq;
      pc[1] <= execRedirect.first;
      epoch <= !epoch;
    end
    else begin
	f2d.enq(Fetch2Decode{inst:inst, pc:pc[1], ppc:ppcF, epoch:epoch});
    end*/ 

    f2d.enq(Fetch2Decode{inst:inst, pc:pc[1], ppc:ppcF, epoch:epoch}); 
  endrule

  rule doDecode(csrf.started);
    let inst = f2d.first.inst;
    let pcD = f2d.first.pc;
    let ppcD = f2d.first.ppc;
    let iepoch = f2d.first.epoch;
    f2d.deq;

    let dInst = decode(inst);
    let stall = sb.search1(dInst.src1) || sb.search2(dInst.src2);

    if(!stall) begin
	let rVal1 = isValid(dInst.src1) ? rf.rd1(validValue(dInst.src1)) : ?;
        let rVal2 = isValid(dInst.src2) ? rf.rd2(validValue(dInst.src2)) : ?;
        let csrVal = isValid(dInst.csr) ? csrf.rd(validValue(dInst.csr)) : ?;

	d2e.enq(Decode2Execute{dInst:dInst, pc:pcD, ppc:ppcD, epoch:iepoch, rVal1:rVal1, rVal2:rVal2, csrVal:csrVal});
	sb.insert(dInst.dst);
	pc[1] <= ppcD;
	//f2d.deq;
    end
  endrule

  rule doExecute(csrf.started);
    let dInst = d2e.first.dInst;
    let pcE = d2e.first.pc;
    let ppcE = d2e.first.ppc;
    let iepoch = d2e.first.epoch;
    let rVal1 = d2e.first.rVal1;
    let rVal2 = d2e.first.rVal2;
    let csrVal = d2e.first.csrVal;
    d2e.deq;

    if(iepoch == epoch) begin
	let eInst = exec(dInst, rVal1, rVal2, pcE, ppcE, csrVal);
	let nextPC = eInst.brTaken ? eInst.addr : pcE + 4;
	if(ppcE != nextPC) begin
	    pc[0] <= eInst.addr;
	    epoch <= !epoch;
	    //execRedirect.enq(eInst.addr);
    	end
        e2m.enq(Execute2Memory{eInst:eInst, pc:pcE, ppc:ppcE, epoch:iepoch});
    		    
        //if(eInst.mispredict) begin
            //execRedirect.enq(eInst.addr);
            //pc[0] <= eInst.addr;
	    //epoch <= !epoch;
        //end
	//else begin
	    //e2m.enq(Execute2Memory{eInst:eInst, pc:pcE, ppc:ppcE, epoch:iEpoch});
    	//end
	//let nextPC = eInst.brTaken ? eInst.addr : pc+4;
	/*if(eInst.mispredict) begin
	    eEpoch <= !eEpoch;
	    execRedirect.enq(eInst.addr);
	    pc[0] <= eInst.addr;
    	end*/
    end
  endrule

  rule doMemory(csrf.started);
    let eInst = e2m.first.eInst;
    let pcM = e2m.first.pc;
    let ppcM = e2m.first.ppc;
    let iepoch = e2m.first.epoch;
    e2m.deq;

    //if(iepoch == epoch) begin
      case(eInst.iType)
	Ld :
        begin
        let d <- dMem.req(MemReq{op: Ld, addr: eInst.addr, data: ?});
        eInst.data = d;
        end

        St:
        begin
        let d <- dMem.req(MemReq{op: St, addr: eInst.addr, data: eInst.data});
        end

        Unsupported :
        begin
        $fwrite(stderr, "ERROR: Executing unsupported instruction\n");
        $finish;
        end
      endcase
    //end

    m2w.enq(Memory2Writeback{eInst:eInst, pc:pcM, ppc:ppcM, epoch:iepoch});
  endrule

  rule doWriteback(csrf.started);
    let eInst   = m2w.first.eInst;
    let pcW   = m2w.first.pc;
    let ppcW    = m2w.first.ppc;
    let iepoch = m2w.first.epoch;
    m2w.deq;

    //if(iepoch == epoch) begin
      if(isValid(eInst.dst)) begin
        rf.wr(fromMaybe(?, eInst.dst), eInst.data);
	//sb.remove;
      end
      csrf.wr(eInst.iType == Csrw ? eInst.csr : Invalid, eInst.data);
    
      sb.remove;
    //end
  endrule

  method ActionValue#(CpuToHostData) cpuToHost;
    let retV <- csrf.cpuToHost;
    return retV;
  endmethod

  method Action hostToCpu(Bit#(32) startpc) if (!csrf.started);
    csrf.start(0);
    epoch <= False;
    //eEpoch <= False;
    //fEpoch <= False;
    pc[1] <= startpc;
  endmethod

  interface iMemInit = iMem.init;
  interface dMemInit = dMem.init;

endmodule
