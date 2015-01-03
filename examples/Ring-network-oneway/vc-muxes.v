//========================================================================
// Verilog Components: Muxes
//========================================================================

`ifndef VC_MUXES_V
`define VC_MUXES_V

//------------------------------------------------------------------------
// 2 Input Mux
//------------------------------------------------------------------------
module vc_Mux2_normal
#(
	parameter p_nbits = 1
)(
	input	  [p_nbits-1:0]					in0,
	input	  [p_nbits-1:0]					in1,
	input									sel,
	output	  [p_nbits-1:0]					out
);
	always @(*)	
	begin
		case ( sel )
			1'd0 : out = in0;
			1'd1 : out = in1;
			default : out = {p_nbits{1'bx}};
		endcase
	end

endmodule

//------------------------------------------------------------------------
// 2 Input Mux
//------------------------------------------------------------------------
module vc_Mux2
#(
  parameter	p_nbits	= 1
)(
  input		[p_nbits-1:0]	{Domain	domain}	in0,
  input		[p_nbits-1:0]	{Domain domain}	in1,
  input						{Domain domain} sel,
  input						{L}				domain,
  output reg[p_nbits-1:0]	{Domain domain}	out
);

  always @(*)
  begin
  	case ( sel )
	  1'd0 : out = in0;
	  1'd1 : out = in1;
	  default : out = {p_nbits{1'bx}};
	endcase
  end

endmodule

// 2 Input Mux with Timing Channel Protection
//------------------------------------------------------------------------

module vc_Mux2_TP
#(
  parameter p_nbits = 1
)(
  input      [p_nbits-1:0] {D1}			in0,
  input		 [p_nbits-1:0] {D2}			in1,
  input                    {L}			sel,
  output reg [p_nbits-1:0] {Domain sel}	out
);

  always @(*)
  begin
    case ( sel )
      1'd0 : out = in0;
      1'd1 : out = in1;
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 3 Input Mux
//------------------------------------------------------------------------

module vc_Mux3
#(
  parameter p_nbits = 1
)(
  input					   {L}				domain,
  input      [p_nbits-1:0] {Domain domain}	in0, in1, in2,
  input              [1:0] {Domain domain}	sel,
  output reg [p_nbits-1:0] {Domain domain}	out
);

  always @(*)
  begin
    case ( sel )
      2'd0 : out = in0;
      2'd1 : out = in1;
      2'd2 : out = in2;
      default : out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 4 Input Mux
//------------------------------------------------------------------------

module vc_Mux4
#(
  parameter p_nbits = 1
)(
  input      [p_nbits-1:0] in0, in1, in2, in3,
  input              [1:0] sel,
  output reg [p_nbits-1:0] out
);

  always @(*)
  begin
    case ( sel )
      2'd0 : out = in0;
      2'd1 : out = in1;
      2'd2 : out = in2;
      2'd3 : out = in3;
      default : out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 5 Input Mux
//------------------------------------------------------------------------

module vc_Mux5
#(
 parameter p_nbits = 1
)(
  input      [p_nbits-1:0] in0, in1, in2, in3, in4,
  input              [2:0] sel,
  output reg [p_nbits-1:0] out
);

  always @(*)
  begin
    case ( sel )
      3'd0 : out = in0;
      3'd1 : out = in1;
      3'd2 : out = in2;
      3'd3 : out = in3;
      3'd4 : out = in4;
      default : out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 6 Input Mux
//------------------------------------------------------------------------

module vc_Mux6
#(
  parameter p_nbits = 1
)(
  input      [p_nbits-1:0] in0, in1, in2, in3, in4, in5,
  input              [2:0] sel,
  output reg [p_nbits-1:0] out
);

  always @(*)
  begin
    case ( sel )
      3'd0 : out = in0;
      3'd1 : out = in1;
      3'd2 : out = in2;
      3'd3 : out = in3;
      3'd4 : out = in4;
      3'd5 : out = in5;
      default : out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 7 Input Mux
//------------------------------------------------------------------------

module vc_Mux7
#(
  parameter p_nbits = 1
)(
  input      [p_nbits-1:0] in0, in1, in2, in3, in4, in5, in6,
  input              [2:0] sel,
  output reg [p_nbits-1:0] out
);

  always @(*)
  begin
    case ( sel )
      3'd0 : out = in0;
      3'd1 : out = in1;
      3'd2 : out = in2;
      3'd3 : out = in3;
      3'd4 : out = in4;
      3'd5 : out = in5;
      3'd6 : out = in6;
      default : out = {p_nbits{1'bx}};
    endcase
  end

endmodule

//------------------------------------------------------------------------
// 8 Input Mux
//------------------------------------------------------------------------

module vc_Mux8
#(
  parameter p_nbits = 1
)(
  input      [p_nbits-1:0] in0, in1, in2, in3, in4, in5, in6, in7,
  input              [2:0] sel,
  output reg [p_nbits-1:0] out
);

  always @(*)
  begin
    case ( sel )
      3'd0 : out = in0;
      3'd1 : out = in1;
      3'd2 : out = in2;
      3'd3 : out = in3;
      3'd4 : out = in4;
      3'd5 : out = in5;
      3'd6 : out = in6;
      3'd7 : out = in7;
      default : out = {p_nbits{1'bx}};
    endcase
  end

endmodule

`endif /* VC_MUXES_V */

