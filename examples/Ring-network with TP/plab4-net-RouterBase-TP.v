//========================================================================
// plab4-net-RouterBase With Timing Channel Protection
//========================================================================

`ifndef PLAB4_NET_ROUTER_BASE_TP_V
`define PLAB4_NET_ROUTER_BASE_TP_V

`include "vc-crossbars.v"
`include "vc-queues.v"
`include "vc-mem-msgs.v"
`include "vc-net-msgs.v"
`include "vc-muxes.v"
`include "plab4-net-RouterInputCtrl-Arbiter-TP.v"
`include "plab4-net-RouterInputTerminalCtrl-Arbiter-TP.v"
`include "plab4-net-RouterOutputCtrl.v"

module plab4_net_RouterBase_TP
#(
	parameter p_payload_nbits	= 32,
	parameter p_opaque_nbits	= 3,
	parameter p_srcdest_nbits	= 3,

	parameter p_router_id		= 0,
	parameter p_num_routers		= 8,

	// Shorter names, not to be set from outside the module
	parameter p = p_payload_nbits,
	parameter o = p_opaque_nbits,
	parameter s = p_srcdest_nbits,

	parameter c_net_msg_nbits = `VC_NET_MSG_NBITS(p,o,s)
)
(
	input							{L}				clk,
	input							{L}				reset,

	// These two signals indicate current cycle belong to which security
	// domain
	input							{L}				domain,

	// The input signals of a router
	input							{Domain domain}	in0_val_d0,
	output							{D1}			in0_rdy_d0,
	input  [c_net_msg_nbits-1:0]	{Domain domain}	in0_msg_d0,

	input							{Domain domain}	in1_val_d0,
	output							{D1}			in1_rdy_d0,
	input  [c_net_msg_nbits-1:0]	{Domain domain}	in1_msg_d0,

	input							{D1}			in_val_ter_d0,
	output							{D1}			in_rdy_ter_d0,
	input  [c_net_msg_nbits-1:0]	{D1}			in_msg_ter_d0,

	input							{D2}			in_val_ter_d1,
	output							{D2}			in_rdy_ter_d1,
	input  [c_net_msg_nbits-1:0]	{D2}			in_msg_ter_d1,

	input							{Domain domain}	in0_val_d1,
	output							{D2}			in0_rdy_d1,
	input  [c_net_msg_nbits-1:0]	{Domain domain}	in0_msg_d1,

	input							{Domain domain}	in1_val_d1,
	output							{D2}			in1_rdy_d1,
	input  [c_net_msg_nbits-1:0]	{Domain domain}	in1_msg_d1,

    // The output signals of a router
	output							{Domain domain}	out0_val,
	input							{Domain domain}	out0_rdy,
	output [c_net_msg_nbits-1:0]	{Domain domain}	out0_msg,

	output							{Domain domain}	out1_val,
	input							{Domain domain}	out1_rdy,
	output [c_net_msg_nbits-1:0]	{Domain domain}	out1_msg,

	output							{Domain domain}	out_val_ter,
	input							{Domain domain}	out_rdy_ter,
	output [c_net_msg_nbits-1:0]	{Domain domain}	out_msg_ter

);

	//----------------------------------------------------------------------
	// Wires
	//----------------------------------------------------------------------

	wire							{D1}			in0_deq_val_d0;
	wire							{D1}			in0_deq_rdy_d0;
	wire   [c_net_msg_nbits-1:0]	{D1}			in0_deq_msg_d0;

	wire							{D1}			in1_deq_val_d0;
	wire							{D1}			in1_deq_rdy_d0;
	wire   [c_net_msg_nbits-1:0]	{D1}			in1_deq_msg_d0;

	wire							{D1}			in_deq_val_ter_d0;
	wire							{D1}			in_deq_rdy_ter_d0;
	wire   [c_net_msg_nbits-1:0]	{D1}			in_deq_msg_ter_d0;

	wire							{D2}			in_deq_val_ter_d1;
	wire							{D2}			in_deq_rdy_ter_d1;
	wire   [c_net_msg_nbits-1:0]	{D2}			in_deq_msg_ter_d1;

	wire							{D2}			in0_deq_val_d1;
	wire							{D2}			in0_deq_rdy_d1;
	wire   [c_net_msg_nbits-1:0]	{D2}			in0_deq_msg_d1;

	wire							{D2}			in1_deq_val_d1;
	wire							{D2}			in1_deq_rdy_d1;
	wire   [c_net_msg_nbits-1:0]	{D2}			in1_deq_msg_d1;


	//----------------------------------------------------------------------
	// Input Queues
	//----------------------------------------------------------------------

	wire [2:0]						{D1}			num_free_west_d0;
	wire [2:0]						{D1}			num_free_east_d0;

	wire [2:0]						{D2}			num_free_west_d1;
	wire [2:0]						{D2}			num_free_east_d1;
	
	vc_Queue
	#(
	  .p_type			(`VC_QUEUE_NORMAL),
      .p_msg_nbits		(c_net_msg_nbits),
	  .p_num_msgs		(4)
	)
	in0_queue_d0
	(
	  .clk				(clk),
	  .reset			(reset),

	  .domain			(1'b0),
	  .domain_signal	(domain),
	  
	  .enq_val			(in0_val_d0),
	  .enq_rdy			(in0_rdy_d0),
	  .enq_msg			(in0_msg_d0),

	  .deq_val			(in0_deq_val_d0),
	  .deq_rdy			(in0_deq_rdy_d0),
	  .deq_msg			(in0_deq_msg_d0),

	  .num_free_entries	(num_free_west_d0)
	);	  

	vc_Queue
	#(
	  .p_type			(`VC_QUEUE_NORMAL),
      .p_msg_nbits		(c_net_msg_nbits),
	  .p_num_msgs		(4)
	)
	in1_queue_d0
	(
	  .clk				(clk),
	  .reset			(reset),

	  .domain			(1'b0),
	  .domain_signal	(domain),
	  
	  .enq_val			(in1_val_d0),
	  .enq_rdy			(in1_rdy_d0),
	  .enq_msg			(in1_msg_d0),

	  .deq_val			(in1_deq_val_d0),
	  .deq_rdy			(in1_deq_rdy_d0),
	  .deq_msg			(in1_deq_msg_d0),

	  .num_free_entries	(num_free_east_d0)
	);	  

	vc_Queue_ter
	#(
	  .p_type			(`VC_QUEUE_NORMAL),
      .p_msg_nbits		(c_net_msg_nbits),
	  .p_num_msgs		(4)
	)
	in_ter_queue_d0
	(
	  .clk				(clk),
	  .reset			(reset),

	  .domain			(1'b0),
	  
	  .enq_val			(in_val_ter_d0),
	  .enq_rdy			(in_rdy_ter_d0),
	  .enq_msg			(in_msg_ter_d0),

	  .deq_val			(in_deq_val_ter_d0),
	  .deq_rdy			(in_deq_rdy_ter_d0),
	  .deq_msg			(in_deq_msg_ter_d0)

	);	  

	vc_Queue_ter
	#(
	  .p_type			(`VC_QUEUE_NORMAL),
      .p_msg_nbits		(c_net_msg_nbits),
	  .p_num_msgs		(4)
	)
	in_ter_queue_d1
	(
	  .clk				(clk),
	  .reset			(reset),

	  .domain			(1'b1),
	  
	  .enq_val			(in_val_ter_d1),
	  .enq_rdy			(in_rdy_ter_d1),
	  .enq_msg			(in_msg_ter_d1),

	  .deq_val			(in_deq_val_ter_d1),
	  .deq_rdy			(in_deq_rdy_ter_d1),
	  .deq_msg			(in_deq_msg_ter_d1)

	);	  
	
	vc_Queue
	#(
	  .p_type			(`VC_QUEUE_NORMAL),
      .p_msg_nbits		(c_net_msg_nbits),
	  .p_num_msgs		(4)
	)
	in0_queue_d1
	(
	  .clk				(clk),
	  .reset			(reset),

	  .domain			(1'b1),
	  .domain_signal	(domain),
	  
	  .enq_val			(in0_val_d1),
	  .enq_rdy			(in0_rdy_d1),
	  .enq_msg			(in0_msg_d1),

	  .deq_val			(in0_deq_val_d1),
	  .deq_rdy			(in0_deq_rdy_d1),
	  .deq_msg			(in0_deq_msg_d1),

	  .num_free_entries	(num_free_west_d1)
	);	  

	vc_Queue
	#(
	  .p_type			(`VC_QUEUE_NORMAL),
      .p_msg_nbits		(c_net_msg_nbits),
	  .p_num_msgs		(4)
	)
	in1_queue_d1
	(
	  .clk				(clk),
	  .reset			(reset),

	  .domain			(1'b1),
	  .domain_signal	(domain),
	  
	  .enq_val			(in1_val_d1),
	  .enq_rdy			(in1_rdy_d1),
	  .enq_msg			(in1_msg_d1),

	  .deq_val			(in1_deq_val_d1),
	  .deq_rdy			(in1_deq_rdy_d1),
	  .deq_msg			(in1_deq_msg_d1),

	  .num_free_entries	(num_free_east_d1)
	);	  

	//----------------------------------------------------------------------
	// Mux
	//----------------------------------------------------------------------
	wire [c_net_msg_nbits-1:0]	{Domain domain}	in0_deq_msg;
	wire [c_net_msg_nbits-1:0]	{Domain domain}	in1_deq_msg;
	wire [c_net_msg_nbits-1:0]	{Domain domain}	in_ter_deq_msg;

	vc_Mux2_TP
	#(
		.p_nbits		(c_net_msg_nbits)
	)
	in0_deq_mux
	(
		.in0			(in0_deq_msg_d0),
		.in1			(in0_deq_msg_d1),
		.sel			(domain),
		.out			(in0_deq_msg)
	);
	
	vc_Mux2_TP
	#(
		.p_nbits		(c_net_msg_nbits)
	)
	in1_deq_mux
	(
		.in0			(in1_deq_msg_d0),
		.in1			(in1_deq_msg_d1),
		.sel			(domain),
		.out			(in1_deq_msg)
	);

	vc_Mux2_TP
	#(
		.p_nbits		(c_net_msg_nbits)
	)
	in_ter_deq_mux
	(
		.in0			(in_deq_msg_ter_d0),
		.in1			(in_deq_msg_ter_d1),
		.sel			(domain),
		.out			(in_ter_deq_msg)
	);	

		
	//----------------------------------------------------------------------
	// Crossbar
	//----------------------------------------------------------------------
	
	wire [1:0]					{Domain domain}	xbar_sel0;
	wire [1:0]					{Domain domain}	xbar_sel1;
	wire [1:0]					{Domain domain}	xbar_sel2;

	vc_Crossbar3
	#(
	  .p_nbits			(c_net_msg_nbits)
    )
	xbar
	(
	  .domain			(domain),
	  .in0				(in0_deq_msg),
	  .in1				(in_ter_deq_msg),
	  .in2				(in1_deq_msg),

	  .sel0				(xbar_sel0),
	  .sel1				(xbar_sel1),
	  .sel2				(xbar_sel2),

	  .out0				(out0_msg),
	  .out1				(out_msg_ter),
	  .out2				(out1_msg)
	);

	//----------------------------------------------------------------------
	// Input controls
	//----------------------------------------------------------------------


	wire [2:0]				{Domain domain}		out0_reqs;
	wire [2:0]				{Domain domain}		out1_reqs;
	wire [2:0]				{Domain domain}		out_ter_reqs;

	wire [2:0]				{Domain domain}		out0_grants;
	wire [2:0]				{Domain domain}		out1_grants;
	wire [2:0]				{Domain domain}		out_ter_grants;

	wire [s-1:0]			{D1}				dest0_d0;
	wire [s-1:0]			{D1}				dest1_d0;
	wire [s-1:0]			{D1}				dest_ter_d0;

	wire [s-1:0]			{D2}				dest0_d1;
	wire [s-1:0]			{D2}				dest1_d1;
	wire [s-1:0]			{D2}				dest_ter_d1;

	wire [2:0]				{Domain domain}		in0_reqs;
	wire [2:0]				{Domain domain}		in1_reqs;
	wire [2:0]				{Domain domain}		in_ter_reqs;

	wire [2:0]				{Domain domain}		in0_grants;
	wire [2:0]				{Domain domain}		in1_grants;
	wire [2:0]				{Domain domain}		in_ter_grants;

	assign out0_reqs = { in1_reqs[0], in_ter_reqs[0], in0_reqs[0] };
	assign out_ter_reqs = { in1_reqs[1], in_ter_reqs[1], in0_reqs[1] };
	assign out1_reqs = { in1_reqs[2], in_ter_reqs[2], in0_reqs[2] };

	assign in0_grants = { out1_grants[0], out_ter_grants[0], out0_grants[0] };
	assign in_ter_grants = { out1_grants[1], out_ter_grants[1], out0_grants[1] };
	assign in1_grants = { out1_grants[2], out_ter_grants[2], out0_grants[2] };

	assign dest0_d0 = in0_deq_msg_d0[`VC_NET_MSG_DEST_FIELD(p,o,s)];
	assign dest1_d0 = in1_deq_msg_d0[`VC_NET_MSG_DEST_FIELD(p,o,s)];
	assign dest_ter_d0 = in_deq_msg_ter_d0[`VC_NET_MSG_DEST_FIELD(p,o,s)];

	assign dest0_d1 = in0_deq_msg_d1[`VC_NET_MSG_DEST_FIELD(p,o,s)];
	assign dest1_d1 = in1_deq_msg_d1[`VC_NET_MSG_DEST_FIELD(p,o,s)];
	assign dest_ter_d1 = in_deq_msg_ter_d1[`VC_NET_MSG_DEST_FIELD(p,o,s)];

	// Note: to prevent livelocking, the route computation is only done at the
	// terminal input controls, and the other input controls simplely pass the
	// message through
	
	plab4_net_RouterInputCtrl_Arbiter_TP
	#(
	  .p_router_id		(p_router_id),
	  .p_num_routers	(p_num_routers),
	  .p_default_reqs	(3'b100)
	)
	in0_ctrl
	(
	  .dest_d0			(dest0_d0),
	  .dest_d1			(dest0_d1),

	  .in_val_d0		(in0_deq_val_d0),
	  .in_val_d1		(in0_deq_val_d1),
	  .in_rdy_d0		(in0_deq_rdy_d0),
	  .in_rdy_d1		(in0_deq_rdy_d1),

	  .reqs				(in0_reqs),
	  .grants			(in0_grants),

	  .domain			(domain)
	);

	// Note: the following is the input terminal control to prevent deadlock
	
	plab4_net_RouterInputTerminalCtrl_Arbiter_TP
	#(
	  .p_router_id		(p_router_id),
	  .p_num_routers	(p_num_routers),
	  .p_num_free_nbits	(3)
	)
	in_ter_ctrl
	(
	  .dest_d0			(dest_ter_d0),
	  .dest_d1			(dest_ter_d1),

	  .in_val_d0		(in_deq_val_ter_d0),
	  .in_val_d1		(in_deq_val_ter_d1),
	  .in_rdy_d0		(in_deq_rdy_ter_d0),
	  .in_rdy_d1		(in_deq_rdy_ter_d1),

	  .num_free_west_d0	(num_free_west_d0),
	  .num_free_west_d1	(num_free_west_d1),
	  .num_free_east_d0	(num_free_east_d0),
	  .num_free_east_d1	(num_free_east_d1),

	  .reqs				(in_ter_reqs),
	  .grants			(in_ter_grants),

	  .domain			(domain)
	);

	plab4_net_RouterInputCtrl_Arbiter_TP
	#(
	  .p_router_id		(p_router_id),
	  .p_num_routers	(p_num_routers),
	  .p_default_reqs	(3'b001)
	)
	in1_ctrl_d0
	(
	  .dest_d0			(dest1_d0),
	  .dest_d1			(dest1_d1),

	  .in_val_d0		(in1_deq_val_d0),
	  .in_val_d1		(in1_deq_val_d1),
	  .in_rdy_d0		(in1_deq_rdy_d0),
	  .in_rdy_d1		(in1_deq_rdy_d1),

	  .reqs				(in1_reqs),
	  .grants			(in1_grants),

	  .domain			(domain)
	);

	//----------------------------------------------------------------------
	// Output controls
	//----------------------------------------------------------------------
	
	plab4_net_RouterOutputCtrl out0_ctrl
	(
	  .clk				(clk),
	  .reset			(reset),

	  .domain			(domain),

	  .reqs				(out0_reqs),
	  .grants			(out0_grants),

	  .out_val			(out0_val),
	  .out_rdy			(out0_rdy),
	  .xbar_sel			(xbar_sel0)
	);

	plab4_net_RouterOutputCtrl out_ter_ctrl
	(
	  .clk				(clk),
	  .reset			(reset),

	  .domain			(domain),

	  .reqs				(out_ter_reqs),
	  .grants			(out_ter_grants),

	  .out_val			(out_val_ter),
	  .out_rdy			(out_rdy_ter),
	  .xbar_sel			(xbar_sel1)
	);

	plab4_net_RouterOutputCtrl out1_ctrl
	(
	  .clk				(clk),
	  .reset			(reset),

	  .domain			(domain),

	  .reqs				(out1_reqs),
	  .grants			(out1_grants),

	  .out_val			(out1_val),
	  .out_rdy			(out1_rdy),
	  .xbar_sel			(xbar_sel2)
	);


endmodule
`endif /* PLAB4_NET_ROUTER_BASE_TP_V */






