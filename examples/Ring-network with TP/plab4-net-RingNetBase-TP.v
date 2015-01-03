//========================================================================
// plab4-net-RingNetBase With Timing Channel Protection
//========================================================================

`ifndef PLAB4_NET_RING_NET_BASE_TP
`define	PLAB4_NET_RING_NET_BASE_TP

`include "vc-net-msgs.v"
`include "vc-param-utils.v"
`include "vc-queues.v"
`include "vc-muxes.v"
`include "plab4-net-RouterBase-TP.v"

// macros to calculate previous and next router ids

`define PREV(i_) ( ( i_ + c_num_ports - 1 ) % c_num_ports )
`define NEXT(i_) ( ( i_ + 1 ) % c_num_ports )

module plab4_net_RingNetBase_TP
#(
  parameter	p_payload_nbits		=	32,
  parameter	p_opaque_nbits		=	3,
  parameter	p_srcdest_nbits		=	3,

  // Shorter names, not to be set from outside the module
  parameter p = p_payload_nbits,
  parameter o = p_opaque_nbits,
  parameter s = p_srcdest_nbits,

  parameter c_num_ports			=	8,
  parameter c_net_msg_nbits		=	`VC_NET_MSG_NBITS(p,o,s),

  parameter m = c_net_msg_nbits
)
(
  input												{L}				clk,
  input												{L}				reset,

  input  [`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D1}			in_val_d0,
  output [`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D1}			in_rdy_d0,
  input	 [`VC_PORT_PICK_NBITS(m,c_num_ports)-1:0]	{D1}			in_msg_d0,

  output [`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{Domain domain}	out_ter_val,
  input  [`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{Domain domain}	out_ter_rdy,
  output [`VC_PORT_PICK_NBITS(m,c_num_ports)-1:0]	{Domain domain}	out_ter_msg,

  input  [`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D2}			in_val_d1,
  output [`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D2}			in_rdy_d1,
  input	 [`VC_PORT_PICK_NBITS(m,c_num_ports)-1:0]	{D2}			in_msg_d1,

  input												{L}				domain
);

  //----------------------------------------------------------------------
  // Router-router connection wires
  //----------------------------------------------------------------------

  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D1}			in0_val_d0;
  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D1}			in0_rdy_d0;
  wire	[`VC_PORT_PICK_NBITS(m,c_num_ports)-1:0]	{D1}			in0_msg_d0;

  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D1}			in1_val_d0;
  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D1}			in1_rdy_d0;
  wire	[`VC_PORT_PICK_NBITS(m,c_num_ports)-1:0]	{D1}			in1_msg_d0;

  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D2}			in0_val_d1;
  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D2}			in0_rdy_d1;
  wire	[`VC_PORT_PICK_NBITS(m,c_num_ports)-1:0]	{D2}			in0_msg_d1;

  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D2}			in1_val_d1;
  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D2}			in1_rdy_d1;
  wire	[`VC_PORT_PICK_NBITS(m,c_num_ports)-1:0]	{D2}			in1_msg_d1;


  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{Domain domain}	out0_val;
  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{Domain domain}	out0_rdy;
  wire	[`VC_PORT_PICK_NBITS(m,c_num_ports)-1:0]	{Domain domain}	out0_msg;

  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{Domain domain}	out1_val;
  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{Domain domain}	out1_rdy;
  wire	[`VC_PORT_PICK_NBITS(m,c_num_ports)-1:0]	{Domain domain}	out1_msg;

  //----------------------------------------------------------------------
  // Router generation
  //----------------------------------------------------------------------

  genvar i;

  generate
    for ( i = 0; i < c_num_ports; i = i + 1 ) begin: ROUTER

	  plab4_net_RouterBase_TP
	  #(
		.p_payload_nbits	(p_payload_nbits),
		.p_opaque_nbits		(p_opaque_nbits),
		.p_srcdest_nbits	(p_srcdest_nbits),

		.p_router_id		(i),
		.p_num_routers		(c_num_ports)
	  )
	  router
	  (
		.clk				(clk),
		.reset				(reset),

		.domain				(domain),

		.in0_val_d0			(out1_val[`VC_PORT_PICK_FIELD(1,`PREV(i))]),
		.in0_rdy_d0			(in0_rdy_d0[`VC_PORT_PICK_FIELD(1,i)]),
		.in0_msg_d0			(out1_msg[`VC_PORT_PICK_FIELD(m,`PREV(i))]),

		.in_val_ter_d0		(in_val_d0[`VC_PORT_PICK_FIELD(1,i)]),
		.in_rdy_ter_d0		(in_rdy_d0[`VC_PORT_PICK_FIELD(1,i)]),
		.in_msg_ter_d0		(in_msg_d0[`VC_PORT_PICK_FIELD(m,i)]),

		.in1_val_d0			(out0_val[`VC_PORT_PICK_FIELD(1,`NEXT(i))]),
		.in1_rdy_d0			(in1_rdy_d0[`VC_PORT_PICK_FIELD(1,i)]),
		.in1_msg_d0			(out0_msg[`VC_PORT_PICK_FIELD(m,`NEXT(i))]),

		.in0_val_d1			(out1_val[`VC_PORT_PICK_FIELD(1,`PREV(i))]),
		.in0_rdy_d1			(in0_rdy_d1[`VC_PORT_PICK_FIELD(1,i)]),
		.in0_msg_d1			(out1_msg[`VC_PORT_PICK_FIELD(m,`PREV(i))]),

		.in_val_ter_d1		(in_val_d1[`VC_PORT_PICK_FIELD(1,i)]),
		.in_rdy_ter_d1		(in_rdy_d1[`VC_PORT_PICK_FIELD(1,i)]),
		.in_msg_ter_d1		(in_msg_d1[`VC_PORT_PICK_FIELD(m,i)]),

		.in1_val_d1			(out0_val[`VC_PORT_PICK_FIELD(1,`NEXT(i))]),
		.in1_rdy_d1			(in1_rdy_d1[`VC_PORT_PICK_FIELD(1,i)]),
		.in1_msg_d1			(out0_msg[`VC_PORT_PICK_FIELD(m,`NEXT(i))]),

		.out0_val			(out0_val[`VC_PORT_PICK_FIELD(1,i)]),
		.out0_rdy			(out0_rdy[`VC_PORT_PICK_FIELD(1,i)]),
		.out0_msg			(out0_msg[`VC_PORT_PICK_FIELD(m,i)]),

		.out_val_ter		(out_ter_val[`VC_PORT_PICK_FIELD(1,i)]),
		.out_rdy_ter		(out_ter_rdy[`VC_PORT_PICK_FIELD(1,i)]),
		.out_msg_ter		(out_ter_msg[`VC_PORT_PICK_FIELD(m,i)]),

		.out1_val			(out1_val[`VC_PORT_PICK_FIELD(1,i)]),
		.out1_rdy			(out1_rdy[`VC_PORT_PICK_FIELD(1,i)]),
		.out1_msg			(out1_msg[`VC_PORT_PICK_FIELD(m,i)])	
	  );
	
	end
  endgenerate

  //----------------------------------------------------------------------
  // Input data generation
  //----------------------------------------------------------------------

  generate
    for ( i = 0; i < c_num_ports; i = i + 1 ) begin: MUXES
		
		/*vc_Mux2_TP
		#(
			.p_nbits		(1'b1)
		)
		in0_val_d0_mux
		(
			.in1			(1'b0),
			.in0			(out1_val[`VC_PORT_PICK_FIELD(1,`PREV(i))]),
			.sel			(domain),
			.out			(in0_val_d0[`VC_PORT_PICK_FIELD(1,i)])
		);

		vc_Mux2_TP
		#(
			.p_nbits		(m)
		)
		in0_msg_d0_mux
		(
			.in1			(32'bx),
			.in0			(out1_msg[`VC_PORT_PICK_FIELD(m,`PREV(i))]),
			.sel			(domain),
			.out			(in0_msg_d0[`VC_PORT_PICK_FIELD(m,i)])
		);

		vc_Mux2_TP
		#(
			.p_nbits		(1'b1)
		)
		in0_val_d1_mux
		(
			.in0			(1'b0),
			.in1			(out1_val[`VC_PORT_PICK_FIELD(1,`PREV(i))]),
			.sel			(domain),
			.out			(in0_val_d1[`VC_PORT_PICK_FIELD(1,i)])
		);

		vc_Mux2_TP
		#(
			.p_nbits		(m)
		)
		in0_msg_d1_mux
		(
			.in0			(32'bx),
			.in1			(out1_msg[`VC_PORT_PICK_FIELD(m,`PREV(i))]),
			.sel			(domain),
			.out			(in0_msg_d1[`VC_PORT_PICK_FIELD(m,i)])
		);

		vc_Mux2_TP
		#(
			.p_nbits		(1'b1)
		)
		in1_val_d0_mux
		(
			.in1			(1'b0),
			.in0			(out0_val[`VC_PORT_PICK_FIELD(1,`NEXT(i))]),
			.sel			(domain),
			.out			(in1_val_d0[`VC_PORT_PICK_FIELD(1,i)])
		);

		vc_Mux2_TP
		#(
			.p_nbits		(m)
		)
		in1_msg_d0_mux
		(
			.in1			(32'bx),
			.in0			(out0_msg[`VC_PORT_PICK_FIELD(m,`NEXT(i))]),
			.sel			(domain),
			.out			(in1_msg_d0[`VC_PORT_PICK_FIELD(m,i)])
		);

		vc_Mux2_TP
		#(
			.p_nbits		(1'b1)
		)
		in1_val_d1_mux
		(
			.in0			(1'b0),
			.in1			(out0_val[`VC_PORT_PICK_FIELD(1,`NEXT(i))]),
			.sel			(domain),
			.out			(in1_val_d1[`VC_PORT_PICK_FIELD(1,i)])
		);

		vc_Mux2_TP
		#(
			.p_nbits		(m)
		)
		in1_msg_d1_mux
		(
			.in0			(32'b0),
			.in1			(out0_msg[`VC_PORT_PICK_FIELD(m,`NEXT(i))]),
			.sel			(domain),
			.out			(in1_msg_d1[`VC_PORT_PICK_FIELD(m,i)])
		);*/

		vc_Mux2_TP
		#(
			.p_nbits		(1'b1)
		)
		out0_rdy_mux
		(
			.in0			(in1_rdy_d0[`VC_PORT_PICK_FIELD(1,`PREV(i))]),
			.in1			(in1_rdy_d1[`VC_PORT_PICK_FIELD(1,`PREV(i))]),
			.sel			(domain),
			.out			(out0_rdy[`VC_PORT_PICK_FIELD(1,i)])
		);

		vc_Mux2_TP
		#(
			.p_nbits		(1'b1)
		)
		out1_rdy_mux
		(
			.in0			(in0_rdy_d0[`VC_PORT_PICK_FIELD(1,`NEXT(i))]),
			.in1			(in0_rdy_d1[`VC_PORT_PICK_FIELD(1,`NEXT(i))]),
			.sel			(domain),
			.out			(out1_rdy[`VC_PORT_PICK_FIELD(1,i)])
		);

		end
  endgenerate

endmodule
`endif /* PLAB4_NET_RING_NET_BASE_TP */
