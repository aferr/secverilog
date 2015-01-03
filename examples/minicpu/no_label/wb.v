`include "mips.h"

module wb (I4, WBsel, ReadLabel, WriteLabel);
   
   input  [31:0]	I4;	// Stage 5 instruction
   input		 ReadLabel;
   input		 WriteLabel;
   
   output [2:0] 	WBsel;	
   reg    [2:0]		WBsel;	// Stage 5 result select
   
   //---------------------------------------------------------------------
   // Control logic for the WB stage
   // WBsel selects whether the data to be written back should come from 
   // the load unit (LMDR) should be the link PC from a jal or jalr instruction
   // or should be the output of the ALU.
   //---------------------------------------------------------------------
   
   always @(I4) begin
      casex ({I4[`op],I4[`rt], I4[`function]})
	
	// Write back load data from cache
	{`LW, `dc5, `dc6}: WBsel = `select_wb_load;
	{`LHU,`dc5, `dc6}: WBsel = `select_wb_load;
	{`LH, `dc5, `dc6}: WBsel = `select_wb_load;
	{`LBU,`dc5, `dc6}: WBsel = `select_wb_load;
	{`LB, `dc5, `dc6}: WBsel = `select_wb_load;
	
	// Write back PC link value
	{`JAL,`dc5, `dc6}: WBsel = `select_wb_link;
	{`SPECIAL,`dc5, `JALR}: WBsel = `select_wb_link;
	{`REGIMM, `BGEZAL,`dc6}:WBsel = `select_wb_link;
	{`REGIMM, `BGEZAL,`dc6}:WBsel = `select_wb_link;
	
	// Write back result from ALU
	default		 : WBsel = `select_wb_alu;	
      endcase
   end
   
endmodule













