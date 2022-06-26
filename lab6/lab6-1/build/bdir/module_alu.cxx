/*
 * Generated by Bluespec Compiler, version 2021.12.1 (build fd50140)
 * 
 * On Thu Jun  2 21:26:05 KST 2022
 * 
 */
#include "bluesim_primitives.h"
#include "module_alu.h"


/* Constructor */
MOD_module_alu::MOD_module_alu(tSimStateHdl simHdl, char const *name, Module *parent)
  : Module(simHdl, name, parent)
{
  symbol_count = 0u;
  init_symbols_0();
}


/* Symbol init fns */

void MOD_module_alu::init_symbols_0()
{
}


/* Rule actions */


/* Methods */

tUInt32 MOD_module_alu::METH_alu(tUInt32 ARG_alu_a, tUInt32 ARG_alu_b, tUInt8 ARG_alu_func)
{
  tUInt32 DEF_alu_a_PLUS_alu_b___d2;
  tUInt8 DEF_x__h98;
  tUInt8 DEF_x__h90;
  tUInt32 DEF_alu_a_SRL_alu_b_BITS_4_TO_0_8___d21;
  tUInt32 DEF_IF_alu_func_EQ_8_2_THEN_alu_a_SRA_alu_b_BITS_4_ETC___d24;
  tUInt32 DEF_alu_a_SL_alu_b_BITS_4_TO_0_8___d19;
  tUInt32 DEF__0_CONCAT_alu_a_ULT_alu_b_5___d16;
  tUInt32 DEF__0_CONCAT_alu_a_SLT_alu_b_2___d13;
  tUInt32 DEF_alu_a_XOR_alu_b___d10;
  tUInt32 DEF_alu_a_OR_alu_b___d8;
  tUInt32 DEF_alu_a_AND_alu_b___d6;
  tUInt32 DEF_alu_a_MINUS_alu_b___d4;
  tUInt8 DEF_c__h194;
  tUInt32 PORT_alu;
  DEF_c__h194 = (tUInt8)((tUInt8)31u & ARG_alu_b);
  DEF_alu_a_MINUS_alu_b___d4 = ARG_alu_a - ARG_alu_b;
  DEF_alu_a_AND_alu_b___d6 = ARG_alu_a & ARG_alu_b;
  DEF_alu_a_OR_alu_b___d8 = ARG_alu_a | ARG_alu_b;
  DEF_alu_a_XOR_alu_b___d10 = ARG_alu_a ^ ARG_alu_b;
  DEF_alu_a_SL_alu_b_BITS_4_TO_0_8___d19 = primShiftL32(32u,
							32u,
							(tUInt32)(ARG_alu_a),
							5u,
							(tUInt8)(DEF_c__h194));
  DEF_x__h90 = primSLT8(1u, 32u, (tUInt32)(ARG_alu_a), 32u, (tUInt32)(ARG_alu_b));
  DEF__0_CONCAT_alu_a_SLT_alu_b_2___d13 = (tUInt32)(DEF_x__h90);
  DEF_IF_alu_func_EQ_8_2_THEN_alu_a_SRA_alu_b_BITS_4_ETC___d24 = primShiftRA32(32u,
									       32u,
									       (tUInt32)(ARG_alu_a),
									       5u,
									       (tUInt8)(DEF_c__h194));
  DEF_x__h98 = ARG_alu_a < ARG_alu_b;
  DEF__0_CONCAT_alu_a_ULT_alu_b_5___d16 = (tUInt32)(DEF_x__h98);
  DEF_alu_a_SRL_alu_b_BITS_4_TO_0_8___d21 = primShiftR32(32u,
							 32u,
							 (tUInt32)(ARG_alu_a),
							 5u,
							 (tUInt8)(DEF_c__h194));
  DEF_alu_a_PLUS_alu_b___d2 = ARG_alu_a + ARG_alu_b;
  switch (ARG_alu_func) {
  case (tUInt8)0u:
    PORT_alu = DEF_alu_a_PLUS_alu_b___d2;
    break;
  case (tUInt8)1u:
    PORT_alu = DEF_alu_a_MINUS_alu_b___d4;
    break;
  case (tUInt8)2u:
    PORT_alu = DEF_alu_a_AND_alu_b___d6;
    break;
  case (tUInt8)3u:
    PORT_alu = DEF_alu_a_OR_alu_b___d8;
    break;
  case (tUInt8)4u:
    PORT_alu = DEF_alu_a_XOR_alu_b___d10;
    break;
  case (tUInt8)5u:
    PORT_alu = DEF__0_CONCAT_alu_a_SLT_alu_b_2___d13;
    break;
  case (tUInt8)6u:
    PORT_alu = DEF__0_CONCAT_alu_a_ULT_alu_b_5___d16;
    break;
  case (tUInt8)7u:
    PORT_alu = DEF_alu_a_SL_alu_b_BITS_4_TO_0_8___d19;
    break;
  case (tUInt8)9u:
    PORT_alu = DEF_alu_a_SRL_alu_b_BITS_4_TO_0_8___d21;
    break;
  default:
    PORT_alu = DEF_IF_alu_func_EQ_8_2_THEN_alu_a_SRA_alu_b_BITS_4_ETC___d24;
  }
  return PORT_alu;
}

tUInt8 MOD_module_alu::METH_RDY_alu()
{
  tUInt8 PORT_RDY_alu;
  tUInt8 DEF_CAN_FIRE_alu;
  DEF_CAN_FIRE_alu = (tUInt8)1u;
  PORT_RDY_alu = DEF_CAN_FIRE_alu;
  return PORT_RDY_alu;
}


/* Reset routines */


/* Static handles to reset routines */


/* Functions for the parent module to register its reset fns */


/* Functions to set the elaborated clock id */


/* State dumping routine */
void MOD_module_alu::dump_state(unsigned int indent)
{
}


/* VCD dumping routines */

unsigned int MOD_module_alu::dump_VCD_defs(unsigned int levels)
{
  vcd_write_scope_start(sim_hdl, inst_name);
  vcd_num = vcd_reserve_ids(sim_hdl, 0u);
  unsigned int num = vcd_num;
  for (unsigned int clk = 0u; clk < bk_num_clocks(sim_hdl); ++clk)
    vcd_add_clock_def(sim_hdl, this, bk_clock_name(sim_hdl, clk), bk_clock_vcd_num(sim_hdl, clk));
  vcd_write_scope_end(sim_hdl);
  return num;
}

void MOD_module_alu::dump_VCD(tVCDDumpType dt, unsigned int levels, MOD_module_alu &backing)
{
}
