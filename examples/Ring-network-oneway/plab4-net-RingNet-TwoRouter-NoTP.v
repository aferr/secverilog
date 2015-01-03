//========================================================================
// plab4-net-RingNetBase Without Timing Channel Protection ( two routers)
//========================================================================

`ifndef PLAB4_NET_RING_NET_TWOROUTER_NOTP
`define PLAB4_NET_RING_NET_TW0ROUTER_NOTP

`include "vc-net-msgs.v"
`include "vc-param-utils.v"
`include "vc-queues.v"
`include "vc-muxes.v"
`include "plab4-net-RouterBase-NoTP-new.v"


// macros to calculate previous and next router ids

`define PREV(i_) ( ( i_ + c_num_ports - 1 ) % c_num_ports )
`define NEXT(i_) ( ( i_ + 1 ) % c_num_ports )

module plab4_net_RingNet_TwoRouter_NOTP
#(
	parameter p_payload_nbits 	=	32,
	parameter p_opaque_nbits	= 	3,
	parameter p_srdest_nbits	= 	3,

	// Shorter names, not to be set from outside the module
	parameter p = p_payload_nbits,
	parameter o = p_opaque_nbits,
	parameter s = p_srcdest_nbits,

	parameter c_num_ports 		= 	2,
	parameter c_net_msg_nbits	= 	`VC_NET_MSG_NBITS(p,o,s),

	parameter m = c_net_msg_nbits
)
(
	input											{L}							clk,
	input											{L}							reset,

	input											{D1}						in_val_d0_r0,
	output											{D1}						in_rdy_d0_r0,
	input [m-1:0]									{D1}						in_msg_d0_r0,
	
	input											{D1}						in_val_d0_r1,
	output											{D1}						in_rdy_d0_r1,
	input [m-1:0]									{D1}						in_msg_d0_r1,

	input											{D2}						in_val_d1_r0,
	output											{D2}						in_rdy_d1_r0,
	input [m-1:0]									{D2}						in_msg_d1_r0,

	input											{D2}						in_val_d1_r1,
	output											{D2}						in_rdy_d1_r1,
	input [m-1:0]									{D2}						in_msg_d1_r1,

	output											{Domain out_ter_domain_r0} 	out_ter_val_r0,
	input											{Domain out_ter_domain_r0}	out_ter_rdy_r0,
	output[m-1:0]									{Domain out_ter_domain_r0}	out_ter_msg_r0,

	output											{Domain out_ter_domain_r1} 	out_ter_val_r1,
	input											{Domain out_ter_domain_r1}	out_ter_rdy_r1,
	output[m-1:0]									{Domain out_ter_domain_r1}	out_ter_msg_r1
);

//========================================================================
// Logic of router 0
//========================================================================
//========================================================================
// Router-router connection wires
//========================================================================

	reg												{D1}						in0_val_d0_r0;
	wire											{D1}						in0_rdy_d0_r0;
	reg	[m:0]										{D1}						in0_msg_d0_r0;
	
	reg												{D1}						in1_val_d0_r0;
	wire											{D1}						in1_rdy_d0_r0;
	reg	[m:0]										{D1}						in1_msg_d0_r0;

	reg												{D2}						in0_val_d1_r0;
	wire											{D2}						in0_rdy_d1_r0;
	reg	[m:0]										{D2}						in0_msg_d1_r0;

	reg												{D2}						in1_val_d1_r0;
	wire											{D2}						in1_rdy_d1_r0;
	reg [m:0]										{D2}						in1_msg_d1_r0;

	wire											{Domain out0_domain_r0}		out0_val_r0;
	wire											{Domain out0_domain_r0}		out0_rdy_r0;
	wire[m:0]										{Domain out0_domain_r0}		out0_msg_r0;
	wire											{D1}						out0_domain_r0;

	wire											{Domain out1_domain_r0}		out1_val_r0;
	wire											{Domain out1_domain_r0}		out1_rdy_r0;
	wire[m:0]										{Domain out1_domain_r0}		out1_msg_r0;
	wire											{D1}						out1_domain_r0;

	wire											{D1}						out_ter_domain_r0;

//========================================================================
// Router generation
//========================================================================
	
	plab4_net_RouterBase_NOTP_new
	#(
		.p_payload_nbits			(p_payload_nbits),
		.p_opaque_nbits				(p_opaque_nbits),
		.p_srcdest_nbits			(p_srcdest_nbits),

		.p_router_id				(1'b0),
		.p_num_routers				(c_num_ports)
	)
	router0
	(
		.clk						(clk),
		.reset						(reset),

		.in0_val_d0					(in0_val_d0_r0),
		.in0_rdy_d0					(in0_rdy_d0_r0),
		.in0_msg_d0					(in0_msg_d0_r0),

		.in_val_ter_d0				(in_val_d0_r0),
		.in_rdy_ter_d0				(in_rdy_d0_r0),
		.in_msg_ter_d0				(in_msg_d0_r0),

		.in1_val_d0					(in1_val_d0_r0),
		.in1_rdy_d0					(in1_rdy_d0_r0),
		.in1_msg_d0					(in1_msg_d0_r0),
		
		.in0_val_d1					(in0_val_d1_r0),
		.in0_rdy_d1					(in0_rdy_d1_r0),
		.in0_msg_d1					(in0_msg_d1_r0),

		.in_val_ter_d1				(in_val_d1_r0),
		.in_rdy_ter_d1				(in_rdy_d1_r0),
		.in_msg_ter_d1				(in_msg_d1_r0),

		.in1_val_d1					(in1_val_d1_r0),
		.in1_rdy_d1					(in1_rdy_d1_r0),
		.in1_msg_d1					(in1_msg_d1_r0),

		.out0_val					(out0_val_r0),
		.out0_rdy					(out0_rdy_r0),
		.out0_msg					(out0_msg_r0),
		.out0_domain				(out0_domain_r0),

		.out_ter_val				(out_ter_val_r0),
		.out_ter_rdy				(out_ter_rdy_r0),
		.out_ter_msg				(out_ter_msg_r0),
		.out_ter_domain				(out_ter_domain_r0),
		
		.out1_val					(out1_val_r0),
		.out1_rdy					(out1_rdy_r0),
		.out1_msg					(out1_msg_r0),
		.out1_domain				(out1_domain_r0)
	);

//========================================================================
// Input data generation
//========================================================================

	always begin
		if ( out1_domain_r1	== 1'b1 )
			in0_val_d0_r0 = 1'b0;
		else
			in0_val_d0_r0 = out1_val_r1;
	end

	always begin
		if ( out1_domain_r1 == 1'b1 )
			in0_msg_d0_r0 = 32'bx;
		else
			in0_msg_d0_r0 = out1_msg_r1;
	end

	always begin
		if ( out1_domain_r1 == 1'b0 )
			in0_val_d1_r0 = 1'b0;
		else
			in0_val_d1_r0 = out1_val_r1;
	end

	always begin
		if ( out1_domain_r1 == 1'b0 )
			in0_msg_d1_r0 = 32'bx;
		else
			in0_msg_d1_r0 = out1_msg_r1;
	end

	always begin
		if ( out0_domain_r1 == 1'b1 )
			in1_val_d0_r0 = 1'b0;
		else
			in1_val_d0_r0 = out0_val_r1;
	end
	
	always begin
		if ( out0_domain_r1 == 1'b1 )
			in1_msg_d0_r0 = 32'bx;
		else
			in1_msg_d0_r0 = out0_msg_r1;
	end

	always begin
		if ( out0_domain_r1 == 1'b0 )
			in1_val_d1_r0 = 1'b0;
		else
			in1_val_d1_r0 = out0_val_r1;
	end

	always begin
		if ( out0_domain_r1 == 1'b0 )
			in1_msg_d1_r0 = 32'bx;
		else
			in1_msg_d1_r0 = out0_msg_r1;
	end

	always begin
		if ( out0_domain_r1 == 1'b0 )
			out0_rdy_r1 = in1_rdy_d0_r0;
		if ( out0_domain_r1 == 1'b1 )
			out0_rdy_r1 = in1_rdy_d1_r0;
	end

	always begin
		if ( out1_domain_r1 == 1'b0 )
			out1_rdy_r1 = in0_rdy_d0_r0;
		if ( out1_domain_r1 == 1'b1 )
			out1_rdy_r1 = in0_rdy_d1_r0;
	end
	
//========================================================================
// Logic of router 1
//========================================================================
//========================================================================
// Router-router connection wires
//========================================================================

	reg												{D1}						in0_val_d0_r1;
	wire											{D1}						in0_rdy_d0_r1;
	reg	[m:0]										{D1}						in0_msg_d0_r1;
	
	reg												{D1}						in1_val_d0_r1;
	wire											{D1}						in1_rdy_d0_r1;
	reg	[m:0]										{D1}						in1_msg_d0_r1;

	reg												{D2}						in0_val_d1_r1;
	wire											{D2}						in0_rdy_d1_r1;
	reg	[m:0]										{D2}						in0_msg_d1_r1;

	reg												{D2}						in1_val_d1_r1;
	wire											{D2}						in1_rdy_d1_r1;
	reg [m:0]										{D2}						in1_msg_d1_r1;

	wire											{Domain out0_domain_r1}		out0_val_r1;
	wire											{Domain out0_domain_r1}		out0_rdy_r1;
	wire[m:0]										{Domain out0_domain_r1}		out0_msg_r1;
	wire											{D1}						out0_domain_r1;

	wire											{Domain out1_domain_r1}		out1_val_r1;
	wire											{Domain out1_domain_r1}		out1_rdy_r1;
	wire[m:0]										{Domain out1_domain_r1}		out1_msg_r1;
	wire											{D1}						out1_domain_r1;

	wire											{D1}						out_ter_domain_r1;

//========================================================================
// Router generation
//========================================================================
	
	plab4_net_RouterBase_NOTP_new
	#(
		.p_payload_nbits			(p_payload_nbits),
		.p_opaque_nbits				(p_opaque_nbits),
		.p_srcdest_nbits			(p_srcdest_nbits),

		.p_router_id				(1'b0),
		.p_num_routers				(c_num_ports)
	)
	router1
	(
		.clk						(clk),
		.reset						(reset),

		.in0_val_d0					(in0_val_d0_r1),
		.in0_rdy_d0					(in0_rdy_d0_r1),
		.in0_msg_d0					(in0_msg_d0_r1),

		.in_val_ter_d0				(in_val_d0_r1),
		.in_rdy_ter_d0				(in_rdy_d0_r1),
		.in_msg_ter_d0				(in_msg_d0_r1),

		.in1_val_d0					(in1_val_d0_r1),
		.in1_rdy_d0					(in1_rdy_d0_r1),
		.in1_msg_d0					(in1_msg_d0_r1),
		
		.in0_val_d1					(in0_val_d1_r1),
		.in0_rdy_d1					(in0_rdy_d1_r1),
		.in0_msg_d1					(in0_msg_d1_r1),

		.in_val_ter_d1				(in_val_d1_r1),
		.in_rdy_ter_d1				(in_rdy_d1_r1),
		.in_msg_ter_d1				(in_msg_d1_r1),

		.in1_val_d1					(in1_val_d1_r1),
		.in1_rdy_d1					(in1_rdy_d1_r1),
		.in1_msg_d1					(in1_msg_d1_r1),

		.out0_val					(out0_val_r1),
		.out0_rdy					(out0_rdy_r1),
		.out0_msg					(out0_msg_r1),
		.out0_domain				(out0_domain_r1),

		.out_ter_val				(out_ter_val_r1),
		.out_ter_rdy				(out_ter_rdy_r1),
		.out_ter_msg				(out_ter_msg_r1),
		.out_ter_domain				(out_ter_domain_r1),
		
		.out1_val					(out1_val_r1),
		.out1_rdy					(out1_rdy_r1),
		.out1_msg					(out1_msg_r1),
		.out1_domain				(out1_domain_r1)
	);

//========================================================================
// Input data generation
//========================================================================

	always begin
		if ( out1_domain_r0	== 1'b1 )
			in0_val_d0_r1 = 1'b0;
		else
			in0_val_d0_r1 = out1_val_r0;
	end

	always begin
		if ( out1_domain_r0 == 1'b1 )
			in0_msg_d0_r1 = 32'bx;
		else
			in0_msg_d0_r1 = out1_msg_r0;
	end

	always begin
		if ( out1_domain_r0 == 1'b0 )
			in0_val_d1_r1 = 1'b0;
		else
			in0_val_d1_r1 = out1_val_r0;
	end

	always begin
		if ( out1_domain_r0 == 1'b0 )
			in0_msg_d1_r1 = 32'bx;
		else
			in0_msg_d1_r1 = out1_msg_r0;
	end

	always begin
		if ( out0_domain_r0 == 1'b1 )
			in1_val_d0_r1 = 1'b0;
		else
			in1_val_d0_r1 = out0_val_r0;
	end
	
	always begin
		if ( out0_domain_r0 == 1'b1 )
			in1_msg_d0_r1 = 32'bx;
		else
			in1_msg_d0_r1 = out0_msg_r0;
	end

	always begin
		if ( out0_domain_r0 == 1'b0 )
			in1_val_d1_r1 = 1'b0;
		else
			in1_val_d1_r1 = out0_val_r0;
	end

	always begin
		if ( out0_domain_r0 == 1'b0 )
			in1_msg_d1_r1 = 32'bx;
		else
			in1_msg_d1_r1 = out0_msg_r0;
	end

	always begin
		if ( out0_domain_r0 == 1'b0 )
			out0_rdy_r0 = in1_rdy_d0_r1;
		if ( out0_domain_r0 == 1'b1 )
			out0_rdy_r0 = in1_rdy_d1_r1;
	end

	always begin
		if ( out1_domain_r0 == 1'b0 )
			out1_rdy_r0 = in0_rdy_d0_r1;
		if ( out1_domain_r0 == 1'b1 )
			out1_rdy_r0 = in0_rdy_d1_r1;
	end

endmodule
`endif /* PLAB4_NET_RING_NET_TWOROUTER_NOTP */
