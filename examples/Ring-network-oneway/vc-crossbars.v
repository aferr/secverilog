//========================================================================
// Verilog Components: Crossbars
//========================================================================

`ifndef VC_CROSSBARS_V
`define VC_CROSSBARS_V

`include "vc-muxes.v"

//------------------------------------------------------------------------
// 3 input, 3 output crossbar
//------------------------------------------------------------------------

module vc_Crossbar3
#(
  parameter p_nbits = 32
)
(
  input 			   {Domain out0_domain}		out0_domain,
  input				   {Domain out_ter_domain}	out_ter_domain,
  input				   {Domain out1_domain}		out1_domain,

  input  [p_nbits-1:0] {Domain domain}  		in0,
  input  [p_nbits-1:0] {Domain domain}  		in1,
  input  [p_nbits-1:0] {Domain domain} 	 		in2,

  input  [1:0]         {Domain out0_domain}		sel0,
  input  [1:0]         {Domain out_ter_domain}	sel1,
  input  [1:0]         {Domain out1_domain}		sel2,

  output [p_nbits-1:0] {Domain out0_domain}		out0,
  output [p_nbits-1:0] {Domain out_ter_domain}	out1,
  output [p_nbits-1:0] {Domain out1_domain}		out2
);

  vc_Mux3#(p_nbits) out0_mux
  (
  	.domain(domain),
    .in0 (in0),
    .in1 (in1),
    .in2 (in2),
    .sel (sel0),
    .out (out0)
  );

  vc_Mux3#(p_nbits) out1_mux
  (
	.domain(domain),
    .in0 (in0),
    .in1 (in1),
    .in2 (in2),
    .sel (sel1),
    .out (out1)
  );

  vc_Mux3#(p_nbits) out2_mux
  (
  	.domain(domain),
    .in0 (in0),
    .in1 (in1),
    .in2 (in2),
    .sel (sel2),
    .out (out2)
  );

endmodule

`endif /* VC_CROSSBAR_V*/
