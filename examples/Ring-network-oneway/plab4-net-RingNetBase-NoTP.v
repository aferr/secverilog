//========================================================================
// plab4-net-RingNetBase Without Timing Channel Protection
//========================================================================

`ifndef PLAB4_NET_RING_NET_BASE_NOTP
`define	PLAB4_NET_RING_NET_BASE_NOTP

`include "vc-net-msgs.v"
`include "vc-param-utils.v"
`include "vc-queues.v"
`include "vc-muxes.v"
`include "plab4-net-RouterBase-NoTP-new.v"
//`include "plab4-net-RouterBase-NoTP.v"

// macros to calculate previous and next router ids

`define PREV(i_) ( ( i_ + c_num_ports - 1 ) % c_num_ports )
`define NEXT(i_) ( ( i_ + 1 ) % c_num_ports )

module plab4_net_RingNetBase_NOTP
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
  input												{L}						clk,
  input												{L}						reset,

  input  [`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D1}					in_val_d0,
  output [`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D1}					in_rdy_d0,
  input	 [`VC_PORT_PICK_NBITS(m,c_num_ports)-1:0]	{D1}					in_msg_d0,

  output [`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{Domain out_ter_domain}	out_ter_val,
  input  [`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{Domain out_ter_domain}	out_ter_rdy,
  output [`VC_PORT_PICK_NBITS(m,c_num_ports)-1:0]	{Domain out_ter_domain}	out_ter_msg,

  input  [`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D2}					in_val_d1,
  output [`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D2}					in_rdy_d1,
  input	 [`VC_PORT_PICK_NBITS(m,c_num_ports)-1:0]	{D2}					in_msg_d1
);

 //----------------------------------------------------------------------
  // Router-router connection wires
  //----------------------------------------------------------------------

  reg	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D1}					in0_val_d0;
  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D1}					in0_rdy_d0;
  reg	[`VC_PORT_PICK_NBITS((m+1),c_num_ports)-1:0]{D1}					in0_msg_d0;

  reg	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D1}					in1_val_d0;
  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D1}					in1_rdy_d0;
  reg	[`VC_PORT_PICK_NBITS((m+1),c_num_ports)-1:0]{D1}					in1_msg_d0;

  reg	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D2}					in0_val_d1;
  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D2}					in0_rdy_d1;
  reg	[`VC_PORT_PICK_NBITS((m+1),c_num_ports)-1:0]{D2}					in0_msg_d1;

  reg	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D2}					in1_val_d1;
  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D2}					in1_rdy_d1;
  reg	[`VC_PORT_PICK_NBITS((m+1),c_num_ports)-1:0]{D2}					in1_msg_d1;


  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{Domain out0_domain}	out0_val;
  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{Domain out0_domain}	out0_rdy;
  wire	[`VC_PORT_PICK_NBITS((m+1),c_num_ports)-1:0]{Domain out0_domain}	out0_msg;
  wire  [`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D1}					out0_domain;

  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{Domain out1_domain}	out1_val;
  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{Domain out1_domain}	out1_rdy;
  wire	[`VC_PORT_PICK_NBITS((m+1),c_num_ports)-1:0]{Domain out1_domain}	out1_msg;
  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D1}					out1_domain;

  wire	[`VC_PORT_PICK_NBITS(1,c_num_ports)-1:0]	{D1}					out_ter_domain;

  //----------------------------------------------------------------------
  // Router generation
  //----------------------------------------------------------------------

  genvar i;

  generate
    for ( i = 0; i < c_num_ports; i = i + 1 ) begin: ROUTER

	  plab4_net_RouterBase_NOTP_new
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

		.in0_val_d0			(in0_val_d0[`VC_PORT_PICK_FIELD(1,i)]),
		.in0_rdy_d0			(in0_rdy_d0[`VC_PORT_PICK_FIELD(1,i)]),
		.in0_msg_d0			(in0_msg_d0[`VC_PORT_PICK_FIELD((m+1),i)]),

		.in_val_ter_d0		(in_val_d0[`VC_PORT_PICK_FIELD(1,i)]),
		.in_rdy_ter_d0		(in_rdy_d0[`VC_PORT_PICK_FIELD(1,i)]),
		.in_msg_ter_d0		(in_msg_d0[`VC_PORT_PICK_FIELD(m,i)]),

		.in1_val_d0			(in1_val_d0[`VC_PORT_PICK_FIELD(1,i)]),
		.in1_rdy_d0			(in1_rdy_d0[`VC_PORT_PICK_FIELD(1,i)]),
		.in1_msg_d0			(in1_msg_d0[`VC_PORT_PICK_FIELD((m+1),i)]),

		.in0_val_d1			(in0_val_d1[`VC_PORT_PICK_FIELD(1,i)]),
		.in0_rdy_d1			(in0_rdy_d1[`VC_PORT_PICK_FIELD(1,i)]),
		.in0_msg_d1			(in0_msg_d1[`VC_PORT_PICK_FIELD((m+1),i)]),

		.in_val_ter_d1		(in_val_d1[`VC_PORT_PICK_FIELD(1,i)]),
		.in_rdy_ter_d1		(in_rdy_d1[`VC_PORT_PICK_FIELD(1,i)]),
		.in_msg_ter_d1		(in_msg_d1[`VC_PORT_PICK_FIELD(m,i)]),

		.in1_val_d1			(in1_val_d1[`VC_PORT_PICK_FIELD(1,i)]),
		.in1_rdy_d1			(in1_rdy_d1[`VC_PORT_PICK_FIELD(1,i)]),
		.in1_msg_d1			(in1_msg_d1[`VC_PORT_PICK_FIELD((m+1),i)]),

		.out0_val			(out0_val[`VC_PORT_PICK_FIELD(1,i)]),
		.out0_rdy			(out0_rdy[`VC_PORT_PICK_FIELD(1,i)]),
		.out0_msg			(out0_msg[`VC_PORT_PICK_FIELD((m+1),i)]),
		.out0_domain		(out0_domain[`VC_PORT_PICK_FIELD(1,i)]),

		.out_ter_val		(out_ter_val[`VC_PORT_PICK_FIELD(1,i)]),
		.out_ter_rdy		(out_ter_rdy[`VC_PORT_PICK_FIELD(1,i)]),
		.out_ter_msg		(out_ter_msg[`VC_PORT_PICK_FIELD(m,i)]),
		.out_ter_domain		(out_ter_domain[`VC_PORT_PICK_FIELD(1,i)]),

		.out1_val			(out1_val[`VC_PORT_PICK_FIELD(1,i)]),
		.out1_rdy			(out1_rdy[`VC_PORT_PICK_FIELD(1,i)]),
		.out1_msg			(out1_msg[`VC_PORT_PICK_FIELD((m+1),i)]),
		.out1_domain		(out1_domain[`VC_PORT_PICK_FIELD(1,i)])	
	  );
	
	end
  endgenerate

  //----------------------------------------------------------------------
  // Input data generation
  //----------------------------------------------------------------------
 
 generate
	for ( i = 0; i < c_num_ports; i = i + 1 ) begin: SELECT
		always @(*)	begin
			//if ( out1_msg[`VC_PORT_PICK_MSB((m+1),`PREV(i))] == 1'b1) 
			  if ( out1_domain[`VC_PORT_PICK_FIELD(1,`PREV(i))] == 1'b1 )
				in0_val_d0[`VC_PORT_PICK_FIELD(1,i)] = 1'b0;
			//else if( out1_msg[`VC_PORT_PICK_MSB((m+1),`PREV(i))] == 1'b0 )
			  else
				in0_val_d0[`VC_PORT_PICK_FIELD(1,i)] = out1_val[`VC_PORT_PICK_FIELD(1,`PREV(i))];
		end

		always @(*) begin
			//if ( out1_msg[`VC_PORT_PICK_MSB((m+1),`PREV(i))] == 1'b1)
			  if ( out1_domain[`VC_PORT_PICK_FIELD(1,`PREV(i))] == 1'b1 )
				in0_msg_d0[`VC_PORT_PICK_FIELD((m+1),i)] = 32'bx;
			//else if ( out1_msg[`VC_PORT_PICK_MSB((m+1),`PREV(i))] == 1'b0 )
			  else
				in0_msg_d0[`VC_PORT_PICK_FIELD((m+1),i)] = out1_msg[`VC_PORT_PICK_FIELD((m+1),`PREV(i))];
		end

		always @(*) begin
			//if ( out1_msg[`VC_PORT_PICK_MSB((m+1),`PREV(i))] == 1'b0)
			  if ( out1_domain[`VC_PORT_PICK_FIELD(1,`PREV(i))] == 1'b0 )
				in0_val_d1[`VC_PORT_PICK_FIELD(1,i)] = 1'b0;
			//else if ( out1_msg[`VC_PORT_PICK_MSB((m+1),`PREV(i))] == 1'b1)
			  else
				in0_val_d1[`VC_PORT_PICK_FIELD(1,i)] = out1_val[`VC_PORT_PICK_FIELD(1,`PREV(i))];	
		end

		always @(*) begin
			//if ( out1_msg[`VC_PORT_PICK_MSB((m+1),`PREV(i))] == 1'b0)
			  if ( out1_domain[`VC_PORT_PICK_FIELD(1,`PREV(i))] == 1'b0 )
				in0_msg_d1[`VC_PORT_PICK_FIELD((m+1),i)] = 32'bx;
			//else if ( out1_msg[`VC_PORT_PICK_MSB((m+1),`PREV(i))] == 1'b1)
			  else
				in0_msg_d1[`VC_PORT_PICK_FIELD((m+1),i)] = out1_msg[`VC_PORT_PICK_FIELD((m+1),`PREV(i))];
		end

		always @(*)	begin
			//if ( out0_msg[`VC_PORT_PICK_MSB((m+1),`NEXT(i))] == 1'b1) 
			  if ( out0_domain[`VC_PORT_PICK_FIELD(1,`NEXT(i))] == 1'b1)
				in1_val_d0[`VC_PORT_PICK_FIELD(1,i)] = 1'b0;
			//else if( out0_msg[`VC_PORT_PICK_MSB((m+1),`NEXT(i))] == 1'b0 )
			  else
				in1_val_d0[`VC_PORT_PICK_FIELD(1,i)] = out0_val[`VC_PORT_PICK_FIELD(1,`NEXT(i))];
		end

		always @(*) begin
			//if ( out0_msg[`VC_PORT_PICK_MSB((m+1),`NEXT(i))] == 1'b1)
			  if ( out0_domain[`VC_PORT_PICK_FIELD(1,`NEXT(i))] == 1'b1)
				in1_msg_d0[`VC_PORT_PICK_FIELD((m+1),i)] = 32'bx;
			//else if ( out0_msg[`VC_PORT_PICK_MSB((m+1),`NEXT(i))] == 1'b0 )
			  else
				in1_msg_d0[`VC_PORT_PICK_FIELD((m+1),i)] = out0_msg[`VC_PORT_PICK_FIELD((m+1),`NEXT(i))];
		end

		always @(*) begin
			//if ( out0_msg[`VC_PORT_PICK_MSB((m+1),`NEXT(i))] == 1'b0)
			  if ( out0_domain[`VC_PORT_PICK_FIELD(1,`NEXT(i))] == 1'b0)
				in1_val_d1[`VC_PORT_PICK_FIELD(1,i)] = 1'b0;
			//else if ( out0_msg[`VC_PORT_PICK_MSB((m+1),`NEXT(i))] == 1'b1)
			  else
				in1_val_d1[`VC_PORT_PICK_FIELD(1,i)] = out0_val[`VC_PORT_PICK_FIELD(1,`NEXT(i))];	
		end

		always @(*) begin
			//if ( out0_msg[`VC_PORT_PICK_MSB((m+1),`NEXT(i))] == 1'b0)
			  if ( out0_domain[`VC_PORT_PICK_FIELD(1,`NEXT(i))] == 1'b0)
				in1_msg_d1[`VC_PORT_PICK_FIELD((m+1),i)] = 32'bx;
			//else if ( out0_msg[`VC_PORT_PICK_MSB((m+1),`NEXT(i))] == 1'b1)
			  else
				in1_msg_d1[`VC_PORT_PICK_FIELD((m+1),i)] = out0_msg[`VC_PORT_PICK_FIELD((m+1),`NEXT(i))];
		end

		always @(*) begin
			if ( out0_domain[`VC_PORT_PICK_FIELD(1,`PREV(i))] == 1'b0 )
				out0_rdy[`VC_PORT_PICK_FIELD(1,i)] = in1_rdy_d0[`VC_PORT_PICK_FIELD(1,`PREV(i))];
			if ( out0_domain[`VC_PORT_PICK_FIELD(1,`PREV(i))] == 1'b1 )
				out0_rdy[`VC_PORT_PICK_FIELD(1,i)] = in1_rdy_d1[`VC_PORT_PICK_FIELD(1,`PREV(i))];
		end

		always @(*) begin
			if ( out1_domain[`VC_PORT_PICK_FIELD(1,`NEXT(i))] == 1'b0 )
				out1_rdy[`VC_PORT_PICK_FIELD(1,i)] = in0_rdy_d0[`VC_PORT_PICK_FIELD(1,`NEXT(i))];
			else
				out1_rdy[`VC_PORT_PICK_FIELD(1,i)] = in0_rdy_d1[`VC_PORT_PICK_FIELD(1,`NEXT(i))];
		end

	end
 endgenerate

 /*generate
    for ( i = 0; i < c_num_ports; i = i + 1 ) begin: MUXES
		
		vc_Mux2
		#(
			.p_nbits		(1'b1)
		)
		out0_rdy_mux
		(
			.in0			(in1_rdy_d0[`VC_PORT_PICK_FIELD(1,`PREV(i))]),
			.in1			(in1_rdy_d1[`VC_PORT_PICK_FIELD(1,`PREV(i))]),
			.sel			(out1_domain[`VC_PORT_PICK_FIELD(1,`PREV(i))]),
			.out			(out0_rdy[`VC_PORT_PICK_FIELD(1,i)])
		);

		vc_Mux2
		#(
			.p_nbits		(1'b1)
		)
		out1_rdy_mux
		(
			.in0			(in0_rdy_d0[`VC_PORT_PICK_FIELD(1,`NEXT(i))]),
			.in1			(in0_rdy_d1[`VC_PORT_PICK_FIELD(1,`NEXT(i))]),
			.sel			(out0_domain[`VC_PORT_PICK_FIELD(1,`NEXT(i))]),
			.out			(out1_rdy[`VC_PORT_PICK_FIELD(1,i)])
		);

		end
  endgenerate*/

endmodule
`endif /* PLAB4_NET_RING_NET_BASE_NOTP */
