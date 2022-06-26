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
  RFile         rf  <- mkBypassRFile; // wr < rd :  Refer to p.20, M10
  //RFile         rf  <- mkRFile;
  IMemory     iMem  <- mkIMemory;
  DMemory     dMem  <- mkDMemory;
  CsrFile     csrf <- mkCsrFile;

  // Control hazard handling Elements : 2 Epoch registers and one BypassFifo
  //Reg#(Bool) fEpoch <- mkRegU;
  //Reg#(Bool) eEpoch <- mkRegU;
  Reg#(Bool) epoch <- mkRegU;

  Fifo#(1, Decode2Execute) d2eRedirect <- mkBypassFifo;
  Fifo#(1, Execute2Memory) e2mRedirect <- mkBypassFifo;
  Fifo#(1, Memory2Writeback) m2wRedirect <- mkBypassFifo;
   
  // Fetch stage -> Rest stage PipelineFifo
  Fifo#(1, Fetch2Decode)  f2d <- mkPipelineFifo;
  Fifo#(1, Decode2Execute)  d2e <- mkPipelineFifo;
  Fifo#(1, Execute2Memory)  e2m <- mkPipelineFifo;
  Fifo#(1, Memory2Writeback)  m2w <- mkPipelineFifo;

 /* TODO:  Lab 6-2: Implement a 5-stage pipelined processor using a bypassing method. 
           Define the proper bypassing units using BypassFiFo */
  rule doFetch(csrf.started);
    let inst = iMem.req(pc[1]);
    let ppcF = pc[1] + 4;

    f2d.enq(Fetch2Decode{inst:inst, pc:pc[1], ppc:ppcF, epoch:epoch}); 
  endrule

  rule doDecode(csrf.started);
    let inst = f2d.first.inst;
    //let d2eRed = d2eRedirect.first.dInst; 
    //d2eRedirect.deq;
    let pcD = f2d.first.pc;
    let ppcD = f2d.first.ppc;
    let iepoch = f2d.first.epoch;
    f2d.deq;

    let stall = False;

    let dInst = decode(inst);
    if(d2eRedirect.notEmpty) begin
	let d2eRed = d2eRedirect.first.dInst; 
        d2eRedirect.deq;
	stall = ((d2eRed.iType == Ld) && ((d2eRed.dst == dInst.src1) || (d2eRed.dst == dInst.src2)));
    end
    
    if(!stall) begin
        let rVal1 = isValid(dInst.src1) ? rf.rd1(validValue(dInst.src1)) : ?;
        let rVal2 = isValid(dInst.src2) ? rf.rd2(validValue(dInst.src2)) : ?;
        let csrVal = isValid(dInst.csr) ? csrf.rd(validValue(dInst.csr)) : ?;
        d2e.enq(Decode2Execute{dInst:dInst, pc:pcD, ppc:ppcD, epoch:iepoch, rVal1:rVal1, rVal2:rVal2, csrVal:csrVal});
        pc[1] <= ppcD;
    end
  endrule

  rule doExecute(csrf.started);
    let dInst = d2e.first.dInst;
    //let e2mRed = e2mRedirect.first.eInst; e2mRedirect.deq;
    //let m2wRed = m2wRedirect.first.eInst; m2wRedirect.deq;
    let pcE = d2e.first.pc;
    let ppcE = d2e.first.ppc;
    let iepoch = d2e.first.epoch;
    let rVal1 = d2e.first.rVal1;
    let rVal2 = d2e.first.rVal2;
    let csrVal = d2e.first.csrVal;
    d2e.deq;
    d2eRedirect.enq(Decode2Execute{dInst:dInst, pc:pcE, ppc:ppcE, epoch:iepoch, rVal1:rVal1, rVal2:rVal2, csrVal:csrVal});

    let forwardA = 2'b00;
    let forwardB = 2'b00;

    if(e2mRedirect.notEmpty) begin
	let e2mRed = e2mRedirect.first.eInst;
	e2mRedirect.deq;
	//EX hazard
        if((e2mRed.dst != tagged Invalid) && (e2mRed.dst==dInst.src1)) begin
            //forwardA = 2'b10;
	    rVal1 = e2mRedirect.first.eInst.data;
        end
        if((e2mRed.dst != tagged Invalid) && (e2mRed.dst==dInst.src2)) begin
            //forwardB = 2'b10;
	    rVal2 = e2mRedirect.first.eInst.data;
        end

        if(m2wRedirect.notEmpty) begin
            let m2wRed = m2wRedirect.first.eInst;
            m2wRedirect.deq;
	    //e2mRedirect.deq;
	    if((m2wRed.dst != tagged Invalid) && !((e2mRed.dst != tagged Invalid) && (e2mRed.dst==dInst.src1)) && (m2wRed.dst==dInst.src1)) begin
                //forwardA = 2'b01;
		rVal1 = m2wRedirect.first.eInst.data;
            end
            if((m2wRed.dst != tagged Invalid) && !((e2mRed.dst != tagged Invalid) && (e2mRed.dst==dInst.src2)) && (m2wRed.dst==dInst.src2)) begin
                //forwardB = 2'b01;
		rVal2 = m2wRedirect.first.eInst.data;
            end
        end
    end
    
    //rVal1 = (forwardA == 2'b10) ? e2mRedirect.first.eInst.data : (forwardA == 2'b01) ? m2wRedirect.first.eInst.data : d2e.first.rVal1;
    //rVal2 = (forwardB == 2'b10) ? e2mRedirect.first.eInst.data : (forwardB == 2'b01) ? m2wRedirect.first.eInst.data : d2e.first.rVal2;

    //e2mRedirect.deq;
    //m2wRedirect.deq;

    //EX hazard
    /*if((e2mRed.dst != tagged Invalid) && (e2mRed.dst==dInst.src1)) begin
	forwardA = 2'b10;
    end
    if((e2mRed.dst != tagged Invalid) && (e2mRed.dst==dInst.src2)) begin
        forwardB = 2'b10;
    end*/

    //MEM hazard
    /*if((m2wRed.dst != tagged Invalid) && !((e2mRed.dst != tagged Invalid) && (e2mRed.dst==dInst.src1)) && (m2wRed.dst==dInst.src1)) begin
        forwardA = 2'b01;
    end 
    if((m2wRed.dst != tagged Invalid) && !((e2mRed.dst != tagged Invalid) && (e2mRed.dst==dInst.src2)) && (m2wRed.dst==dInst.src2)) begin
        forwardB = 2'b01;
    end*/	

    //let rVal1 = (forwardA == 2'b10) ? e2mRed.data : (forwardA == 2'b01) ? m2wRed.data : d2e.first.rVal1;
    //let rVal2 = (forwardB == 2'b10) ? e2mRed.data : (forwardB == 2'b01) ? m2wRed.data : d2e.first.rVal2;

    //d2e.deq;

    //d2eRedirect.enq(Decode2Execute{dInst:dInst, pc:pcE, ppc:ppcE, epoch:iepoch, rVal1:rVal1, rVal2:rVal2, csrVal:csrVal});

    if(iepoch == epoch) begin
        let eInst = exec(dInst, rVal1, rVal2, pcE, ppcE, csrVal);
        let nextPC = eInst.brTaken ? eInst.addr : pcE + 4;
        if(ppcE != nextPC) begin
            pc[0] <= eInst.addr;
            epoch <= !epoch;
        end
        e2m.enq(Execute2Memory{eInst:eInst, pc:pcE, ppc:ppcE, epoch:iepoch});
    end
  endrule

  rule doMemory(csrf.started);
    let eInst = e2m.first.eInst;
    let pcM = e2m.first.pc;
    let ppcM = e2m.first.ppc;
    let iepoch = e2m.first.epoch;
    e2m.deq;

    e2mRedirect.enq(Execute2Memory{eInst:eInst, pc:pcM, ppc:ppcM, epoch:iepoch});

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

    m2w.enq(Memory2Writeback{eInst:eInst, pc:pcM, ppc:ppcM, epoch:iepoch});
  endrule

  rule doWriteback(csrf.started);
    let eInst   = m2w.first.eInst;
    let pcW   = m2w.first.pc;
    let ppcW    = m2w.first.ppc;
    let iepoch = m2w.first.epoch;
    m2w.deq;

    m2wRedirect.enq(Memory2Writeback{eInst:eInst, pc:pcW, ppc:ppcW, epoch:iepoch});

    if(isValid(eInst.dst)) begin
        rf.wr(fromMaybe(?, eInst.dst), eInst.data);
      end
      csrf.wr(eInst.iType == Csrw ? eInst.csr : Invalid, eInst.data);
  endrule

  method ActionValue#(CpuToHostData) cpuToHost;
    let retV <- csrf.cpuToHost;
    return retV;
  endmethod

  method Action hostToCpu(Bit#(32) startpc) if (!csrf.started);
    csrf.start(0);
    //eEpoch <= False;
    //fEpoch <= False;
    epoch <= False;
    pc[1] <= startpc;
  endmethod

  interface iMemInit = iMem.init;
  interface dMemInit = dMem.init;

endmodule
