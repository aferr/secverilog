//========================================================================
// plab4-net-RouterBase Without Timing Channel Protection
//========================================================================

`ifndef PLAB4_NET_ROUTER_BASE_NOTP_V
`define PLAB4_NET_ROUTER_BASE_NOTP_V

`include "vc-queues.v"
`include "vc-mem-msgs.v"
`include "vc-net-msgs.v"
`include "vc-muxes.v"
`include "plab4-net-RouterInputCtrl-Arbiter-NoTP.v"
`include "plab4-net-RouterInputTerminalCtrl-Arbiter-NoTP.v"
`include "plab4-net-RouterOutputCtrl.v"

module plab4_net_RouterBase_NOTP_new
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
	input							{L}						clk,
	input							{L}						reset,

	// The input signals of a router
	input							{D1}					in0_val_d0,
	output							{D1}					in0_rdy_d0,
	input  [c_net_msg_nbits:0]		{D1}					in0_msg_d0,

	input							{D1}					in1_val_d0,
	output							{D1}					in1_rdy_d0,
	input  [c_net_msg_nbits:0]		{D1}					in1_msg_d0,

	input							{D1}					in_val_ter_d0,
	output							{D1}					in_rdy_ter_d0,
	input  [c_net_msg_nbits-1:0]	{D1}					in_msg_ter_d0,

	input							{D2}					in_val_ter_d1,
	output							{D2}					in_rdy_ter_d1,
	input  [c_net_msg_nbits-1:0]	{D2}					in_msg_ter_d1,

	input							{D2}					in0_val_d1,
	output							{D2}					in0_rdy_d1,
	input  [c_net_msg_nbits:0]		{D2}					in0_msg_d1,

	input							{D2}					in1_val_d1,
	output							{D2}					in1_rdy_d1,
	input  [c_net_msg_nbits:0]		{D2}					in1_msg_d1,

	// The output signals of a router
	output							{Domain out0_domain}	out0_val,
	input							{Domain out0_domain}	out0_rdy,
	output [c_net_msg_nbits:0]		{Domain out0_domain}	out0_msg,
	output							{D1}					out0_domain,

	output							{Domain out1_domain}	out1_val,
	input							{Domain out1_domain}	out1_rdy,
	output [c_net_msg_nbits:0]		{Domain out1_domain}	out1_msg,
	output							{D1}					out1_domain,

	output							{Domain out_ter_domain}	out_ter_val,
	input							{Domain out_ter_domain}	out_ter_rdy,
	output [c_net_msg_nbits-1:0]	{Domain out_ter_domain}	out_ter_msg,
	output							{D1}					out_ter_domain
);

	//----------------------------------------------------------------------
	// Wires
	//----------------------------------------------------------------------

	wire							{D1}					in0_deq_val_d0;
	wire							{D1}					in0_deq_rdy_d0;
	wire   [c_net_msg_nbits-1:0]	{D1}					in0_deq_msg_d0;

	wire							{D1}					in1_deq_val_d0;
	wire							{D1}					in1_deq_rdy_d0;
	wire   [c_net_msg_nbits-1:0]	{D1}					in1_deq_msg_d0;

	wire							{D1}					in_deq_val_ter_d0;
	wire							{D1}					in_deq_rdy_ter_d0;
	wire   [c_net_msg_nbits-1:0]	{D1}					in_deq_msg_ter_d0;

	wire							{D2}					in_deq_val_ter_d1;
	wire							{D2}					in_deq_rdy_ter_d1;
	wire   [c_net_msg_nbits-1:0]	{D2}					in_deq_msg_ter_d1;

	wire							{D2}					in0_deq_val_d1;
	wire							{D2}					in0_deq_rdy_d1;
	wire   [c_net_msg_nbits-1:0]	{D2}					in0_deq_msg_d1;

	wire							{D2}					in1_deq_val_d1;
	wire							{D2}					in1_deq_rdy_d1;
	wire   [c_net_msg_nbits-1:0]	{D2}					in1_deq_msg_d1;

	//----------------------------------------------------------------------
	// Input Queues
	//----------------------------------------------------------------------

	wire [3:0]						{D1}					num_free_west_d0;
	wire [3:0]						{D1}					num_free_east_d0;

	wire [3:0]						{D2}					num_free_west_d1;
	wire [3:0]						{D2}					num_free_east_d1;
	
	wire [c_net_msg_nbits-1:0]		{D1}					in0_msg_d0_enq;
	wire [c_net_msg_nbits-1:0]		{D1}					in1_msg_d0_enq;
	wire [c_net_msg_nbits-1:0]		{D2}					in0_msg_d1_enq;
	wire [c_net_msg_nbits-1:0]		{D2}					in1_msg_d1_enq;

	assign	in0_msg_d0_enq = in0_msg_d0[c_net_msg_nbits-1:0];
	assign	in1_msg_d0_enq = in1_msg_d0[c_net_msg_nbits-1:0];
	assign  in0_msg_d1_enq = in0_msg_d1[c_net_msg_nbits-1:0];
	assign	in1_msg_d1_enq = in1_msg_d1[c_net_msg_nbits-1:0];

	vc_Queue
	#(
	  .p_type			(`VC_QUEUE_NORMAL),
      .p_msg_nbits		(c_net_msg_nbits),
	  .p_num_msgs		(8)
	)
	in0_queue_d0
	(
	  .clk				(clk),
	  .reset			(reset),

	  .domain			(1'b0),
	  .domain_signal	(1'b0),
	  
	  .enq_val			(in0_val_d0),
	  .enq_rdy			(in0_rdy_d0),
	  .enq_msg			(in0_msg_d0_enq),

	  .deq_val			(in0_deq_val_d0),
	  .deq_rdy			(in0_deq_rdy_d0),
	  .deq_msg			(in0_deq_msg_d0),

	  .num_free_entries	(num_free_west_d0)
	);	  

	vc_Queue
	#(
	  .p_type			(`VC_QUEUE_NORMAL),
      .p_msg_nbits		(c_net_msg_nbits),
	  .p_num_msgs		(8)
	)
	in1_queue_d0
	(
	  .clk				(clk),
	  .reset			(reset),

	  .domain			(1'b0),
	  .domain_signal	(1'b0),
	  
	  .enq_val			(in1_val_d0),
	  .enq_rdy			(in1_rdy_d0),
	  .enq_msg			(in1_msg_d0_enq),

	  .deq_val			(in1_deq_val_d0),
	  .deq_rdy			(in1_deq_rdy_d0),
	  .deq_msg			(in1_deq_msg_d0),

	  .num_free_entries	(num_free_east_d0)
	);	  

	vc_Queue
	#(
	  .p_type			(`VC_QUEUE_NORMAL),
      .p_msg_nbits		(c_net_msg_nbits),
	  .p_num_msgs		(8)
	)
	in_ter_queue_d0
	(
	  .clk				(clk),
	  .reset			(reset),

	  .domain			(1'b0),
	  .domain_signal	(1'b0),
	  
	  .enq_val			(in_val_ter_d0),
	  .enq_rdy			(in_rdy_ter_d0),
	  .enq_msg			(in_msg_ter_d0),

	  .deq_val			(in_deq_val_ter_d0),
	  .deq_rdy			(in_deq_rdy_ter_d0),
	  .deq_msg			(in_deq_msg_ter_d0)

	);	  

	vc_Queue
	#(
	  .p_type			(`VC_QUEUE_NORMAL),
      .p_msg_nbits		(c_net_msg_nbits),
	  .p_num_msgs		(8)
	)
	in_ter_queue_d1
	(
	  .clk				(clk),
	  .reset			(reset),

	  .domain			(1'b1),
	  .domain_signal	(1'b1),
	  
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
	  .p_num_msgs		(8)
	)
	in0_queue_d1
	(
	  .clk				(clk),
	  .reset			(reset),

	  .domain			(1'b1),
	  .domain_signal	(1'b1),
	  
	  .enq_val			(in0_val_d1),
	  .enq_rdy			(in0_rdy_d1),
	  .enq_msg			(in0_msg_d1_enq),

	  .deq_val			(in0_deq_val_d1),
	  .deq_rdy			(in0_deq_rdy_d1),
	  .deq_msg			(in0_deq_msg_d1),

	  .num_free_entries	(num_free_west_d1)
	);	  

	vc_Queue
	#(
	  .p_type			(`VC_QUEUE_NORMAL),
      .p_msg_nbits		(c_net_msg_nbits),
	  .p_num_msgs		(8)
	)
	in1_queue_d1
	(
	  .clk				(clk),
	  .reset			(reset),

	  .domain			(1'b1),
	  .domain_signal	(1'b1),
	  
	  .enq_val			(in1_val_d1),
	  .enq_rdy			(in1_rdy_d1),
	  .enq_msg			(in1_msg_d1_enq),

	  .deq_val			(in1_deq_val_d1),
	  .deq_rdy			(in1_deq_rdy_d1),
	  .deq_msg			(in1_deq_msg_d1),

	  .num_free_entries	(num_free_east_d1)
	);	 

	//----------------------------------------------------------------------
	// Mux
	//----------------------------------------------------------------------
	reg	[c_net_msg_nbits:0]		{Domain in0_cur_domain}		in0_deq_msg;
	reg	[c_net_msg_nbits:0]		{Domain in1_cur_domain}		in1_deq_msg;
	reg	[c_net_msg_nbits:0]		{Domain in_ter_cur_domain}	in_ter_deq_msg;

	always @(*) begin
		if (in0_cur_domain == 1'b0 ) 
			in0_deq_msg = { 1'b0, in0_deq_msg_d0 };
		else if ( in0_cur_domain == 1'b1 )
			in0_deq_msg = { 1'b1, in0_deq_msg_d1 };
	end

	always @(*) begin
		if (in1_cur_domain == 1'b0)
			in1_deq_msg = { 1'b0, in1_deq_msg_d0 };
		else if ( in1_cur_domain == 1'b1)
			in1_deq_msg = { 1'b1, in1_deq_msg_d1 };
	end

	always @(*) begin
		if (in_ter_cur_domain == 1'b0)
			in_ter_deq_msg = { 1'b0, in_deq_msg_ter_d0 };
		else if (in_ter_cur_domain == 1'b1)
			in_ter_deq_msg = { 1'b1, in_deq_msg_ter_d1 };
	end

	//----------------------------------------------------------------------
	// Crossbar
	//----------------------------------------------------------------------

	wire [1:0]						{Domain out0_domain}	xbar_sel0;
	wire [1:0]						{Domain out_ter_domain}	xbar_sel1;
	wire [1:0]						{Domain out1_domain}	xbar_sel2;
		
	wire [c_net_msg_nbits:0]		{Domain out0_domain}	out0_msg_ex;
	wire [c_net_msg_nbits:0]		{Domain out1_domain}	out1_msg_ex;
	wire [c_net_msg_nbits:0]		{Domain out_ter_domain}	out_ter_msg_ex;

	always @(*) begin
		if ( xbar_sel0 == 2'd0 && ( in0_cur_domain == out0_domain) )
			out0_msg_ex = in0_deq_msg;

		else if ( xbar_sel0 == 2'd1 && ( in_ter_cur_domain == out0_domain) )
			out0_msg_ex = in_ter_deq_msg;

		else if ( xbar_sel0 == 2'd2 && ( in1_cur_domain == out0_domain ) )
			out0_msg_ex = in1_deq_msg;
	end

	always @(*) begin
		if ( xbar_sel1 == 2'd0 && ( in0_cur_domain == out_ter_domain ) )
			out_ter_msg_ex = in0_deq_msg;

		else if ( xbar_sel1 == 2'd1 && ( in_ter_cur_domain == out_ter_domain) )
			out_ter_msg_ex = in_ter_deq_msg;

		else if ( xbar_sel1 == 2'd2 && ( in1_cur_domain == out_ter_domain ) )
			out_ter_msg_ex = in1_deq_msg;
	end

	always @(*) begin
		if ( xbar_sel2 == 2'd0 && ( in0_cur_domain == out1_domain ) )
			out1_msg_ex = in0_deq_msg;
		
		else if ( xbar_sel2 == 2'd1 && ( in_ter_cur_domain == out1_domain ) )
			out1_msg_ex = in_ter_deq_msg;

		else if ( xbar_sel2 == 2'd2 && ( in1_cur_domain == out1_domain ) )
			out1_msg_ex = in1_deq_msg;
	end


	assign out_ter_msg = out_ter_msg_ex[c_net_msg_nbits-1:0];
	assign out0_msg = out0_msg_ex;
	assign out1_msg = out1_msg_ex;

	//assign out0_domain		= out0_msg_ex[c_net_msg_nbits];
	//assign out_ter_domain	= out_ter_msg_ex[c_net_msg_nbits];
    	//assign out1_domain		= out1_msg_ex[c_net_msg_nbits];	

	//----------------------------------------------------------------------
	// Input controls
	//----------------------------------------------------------------------

	wire [2:0]						{Domain out0_domain}		out0_reqs;
	wire [2:0]						{Domain out1_domain}		out1_reqs;
	wire [2:0]						{Domain out_ter_domain}		out_ter_reqs;

	reg  [2:0]						{Domain out0_domain}		out0_reqs_m;
	reg  [2:0]						{Domain out1_domain}		out1_reqs_m;
	reg  [2:0]						{Domain out_ter_domain}		out_ter_reqs_m;

	wire [2:0]						{Domain out0_domain}		out0_grants;
	wire [2:0]						{Domain out1_domain}		out1_grants;
	wire [2:0]						{Domain out_ter_domain}		out_ter_grants;

	wire [s-1:0]					{D1}						dest0_d0;
	wire [s-1:0]					{D1}						dest1_d0;
	wire [s-1:0]					{D1}						dest_ter_d0;

	wire [s-1:0]					{D2}						dest0_d1;
	wire [s-1:0]					{D2}						dest1_d1;
	wire [s-1:0]					{D2}						dest_ter_d1;

	wire [2:0]						{Domain in0_cur_domain}		in0_reqs;
	wire [2:0]						{Domain in1_cur_domain}		in1_reqs;
	wire [2:0]						{Domain in_ter_cur_domain}	in_ter_reqs;

	wire [2:0]						{Domain in0_cur_domain}		in0_grants;
	wire [2:0]						{Domain in1_cur_domain}		in1_grants;
	wire [2:0]						{Domain in_ter_cur_domain}	in_ter_grants;

	reg  [2:0]						{Domain in0_cur_domain}		in0_grants_m;
	reg  [2:0]						{Domain in1_cur_domain}		in1_grants_m;
	reg  [2:0]						{Domain in_ter_cur_domain}	in_ter_grants_m;

	wire							{D1}						in0_cur_domain;
	wire							{D1}						in1_cur_domain;
	wire							{D1}						in_ter_cur_domain;

	// The logic to determine the domain of output1
	always @(*) begin
		out1_domain = 1'b1;
		if ( in0_cur_domain == 1'b0 && in0_reqs == 3'b100 )
			out1_domain = 1'b0;

		if ( in_ter_cur_domain == 1'b0 && in_ter_reqs == 3'b100 )
			out1_domain = 1'b0;

		if ( in0_cur_domain == 1'b1 && in_ter_cur_domain == 1'b1 )
			out1_domain = 1'b1;
	end

	// Calculating the value of reqs sent to output1 control unit
	always @(*) begin
		if ( out1_domain == 1'b0 ) begin
			out1_reqs_m[0] = 1'b0;
			out1_reqs_m[1] = 1'b0;
			out1_reqs_m[2] = 1'b0;
			if ( in_ter_cur_domain == 1'b0 && in_ter_reqs == 3'b100 )
				out1_reqs_m[1] = 1'b1;
			else if ( in_ter_cur_domain == 1'b0 && in_ter_reqs == 3'b001)
				in_ter_grants_m[2] = 1'b0;
			
			if ( in0_cur_domain == 1'b0 && in0_reqs == 3'b100 )
				out1_reqs_m[0] = 1'b1;

			else if ( in0_cur_domain == 1'b0 && in0_reqs == 3'b010)
				in0_grants_m[2] = 1'b0;
		end

		else if ( out1_domain == 1'b1 ) begin
			out1_reqs_m[0] = 1'b0;
			out1_reqs_m[1] = 1'b0;
			out1_reqs_m[2] = 1'b0;
			if ( in0_cur_domain == 1'b1 && in0_reqs == 3'b100 )
				out1_reqs_m[0] = 1'b1;

			if ( in_ter_cur_domain == 1'b1 && in_ter_reqs == 3'b100 )
				out1_reqs_m[1] = 1'b1;
		end
	end
	
	// The logic to determine the domain of output0
	always @(*) begin
		out0_domain = 1'b1;
		if ( in1_cur_domain == 1'b0 && in1_reqs == 3'b001 )
			out0_domain = 1'b0;

		if ( in_ter_cur_domain == 1'b0 && in_ter_reqs == 3'b001 ) 
			out0_domain = 1'b0;

		if ( in1_cur_domain == 1'b1 && in_ter_cur_domain == 1'b1 )
			out0_domain = 1'b1;
	end

	// Calculating the value of reqs sent to output0 control unit
	always @(*) begin
		if ( out0_domain == 1'b0 ) begin
			out0_reqs_m[0] = 1'b0;
			out0_reqs_m[1] = 1'b0;
			out0_reqs_m[2] = 1'b0;
			if ( in_ter_cur_domain == 1'b0 && in_ter_reqs == 3'b001 )
				out0_reqs_m[1] = 1'b1;

			else if ( in_ter_cur_domain == 1'b0 && in_ter_reqs == 3'b100 )
				in_ter_grants_m[0] = 1'b0;
			
			if ( in1_cur_domain == 1'b0 && in1_reqs == 3'b001 )
				out0_reqs_m[2] = 1'b1;

			else if ( in1_cur_domain == 1'b0 && in1_reqs == 3'b010)
				in1_grants_m[0] = 1'b0;
		end

		else if ( out1_domain == 1'b1) begin
			out0_reqs_m[0] = 1'b0;
			out0_reqs_m[1] = 1'b0;
			out0_reqs_m[2] = 1'b0;
			if ( in_ter_cur_domain == 1'b1 && in_ter_reqs == 3'b001 )
				out0_reqs_m[1] = 1'b1;
			
			if ( in1_cur_domain == 1'b1 && in1_reqs == 3'b001 )
				out0_reqs_m[2] = 1'b1;
		end
	end

	// The logic is to determine the domain of terminal output
	always @(*) begin
		out_ter_domain = 1'b1;
		if ( in0_cur_domain == 1'b0 && in0_reqs == 3'b010 )
				out_ter_domain = 1'b0;

		if ( in1_cur_domain == 1'b0 && in1_reqs == 3'b010 )
				out_ter_domain = 1'b0;

		if ( in1_cur_domain == 1'b1 && in0_cur_domain == 1'b1 )
				out_ter_domain = 1'b1;
	end

	// Calculating the value of reqs sent to output terminal control unit
	always @(*) begin
		if ( out_ter_domain == 1'b0 ) begin
			out_ter_reqs_m[0] = 1'b0;
			out_ter_reqs_m[1] = 1'b0;
			out_ter_reqs_m[2] = 1'b0;
			if ( in0_cur_domain == 1'b0 && in0_reqs == 3'b010 )
					out_ter_reqs_m[0] = 1'b1;

			else if ( in0_cur_domain == 1'b0 && in0_reqs == 3'b100 )
					in0_grants_m[1] = 1'b0;

			if ( in1_cur_domain == 1'b0 && in1_reqs == 3'b010 )
					out_ter_reqs_m[2] = 1'b1;

			else if ( in1_cur_domain == 1'b0 && in1_reqs == 3'b001 )
					in1_grants_m[1] = 1'b0;
		end

		else if ( out_ter_domain == 1'b1 ) begin
			out_ter_reqs_m[0] = 1'b0;
			out_ter_reqs_m[1] = 1'b0;
			out_ter_reqs_m[2] = 1'b0;
			if ( in0_cur_domain == 1'b1 && in0_reqs == 3'b010 )
					out_ter_reqs_m[0] = 1'b1;

			if ( in1_cur_domain == 1'b1 && in1_reqs == 3'b010 )
					out_ter_reqs_m[2] = 1'b1;
		end
	end

	assign out0_reqs	= out0_reqs_m;
	assign out_ter_reqs = out_ter_reqs_m;
	assign out1_reqs	= out1_reqs_m;
	
	always @(*) begin
		if ( out0_grants == 3'b100 && out0_domain == 1'b0) begin 
			in1_grants_m = 3'b001;
			in_ter_grants_m[0] = 1'b0;
		end

		else if ( out0_grants == 3'b100 && out0_domain == 1'b1) begin
			if ( in1_cur_domain == 1'b1 )
				in1_grants_m = 3'b001;
			if ( in_ter_cur_domain == 1'b1 )
				in_ter_grants_m[0] = 1'b0;
		end
		
		else if ( out0_grants == 3'b010 && out0_domain == 1'b0) begin
			in_ter_grants_m = 3'b001;
			in1_grants_m[0] = 1'b0;
		end

		else if ( out0_grants == 3'b010 && out0_domain == 1'b1) begin
			if ( in_ter_cur_domain == 1'b1 )
				in_ter_grants_m = 3'b001;
			if ( in1_cur_domain == 1'b1 )
				in1_grants_m[0] = 1'b0;
		end

		else if ( out0_grants == 3'b000 && out0_domain == 1'b0 ) begin
			in1_grants_m[0] = 1'b0;
			in_ter_grants_m[0] = 1'b0;
		end

		else if ( out0_grants == 3'b000 && out0_domain == 1'b1 ) begin
			if ( in1_cur_domain == 1'b1 )
				in1_grants_m[0] = 1'b0;
			if ( in_ter_cur_domain == 1'b1 )
				in_ter_grants_m[0] = 1'b0;
		end
	end	

	always @(*) begin
		if ( out_ter_grants == 3'b100 && out_ter_domain == 1'b0 ) begin
			in1_grants_m = 3'b010;
			in0_grants_m[1] = 1'b0;
		end

		else if ( out_ter_grants == 3'b100 && out_ter_domain == 1'b1 ) begin
			if ( in1_cur_domain == 1'b1 )
				in1_grants_m = 3'b010;
			if ( in0_cur_domain == 1'b1 )
				in0_grants_m[1] = 1'b0;
		end

		else if ( out_ter_grants == 3'b001 && out_ter_domain == 1'b0) begin
			in0_grants_m = 3'b010;
			in1_grants_m[1] = 1'b0;
		end

		else if ( out_ter_grants == 3'b001 && out_ter_domain == 1'b1 ) begin
			if ( in0_cur_domain == 1'b1 )
				in0_grants_m = 3'b010;
			if ( in1_cur_domain == 1'b1 )
				in1_grants_m[1] = 1'b0;
		end

		else if ( out_ter_grants == 3'b000 && out_ter_domain == 1'b0 )begin
			in0_grants_m[1] = 1'b0;
			in1_grants_m[1] = 1'b0;
		end

		else if ( out_ter_grants == 3'b000 && out_ter_domain == 1'b1 ) begin
			if ( in0_cur_domain == 1'b1 )
				in0_grants_m[1] = 1'b0;
			if ( in1_cur_domain == 1'b1 )
				in1_grants_m[1] = 1'b0;
		end
	end

	always @(*) begin
		if ( out1_grants == 3'b001 && out1_domain == 1'b0) begin 
			in0_grants_m = 3'b100;
			in_ter_grants_m[2] = 1'b0;
		end

		else if ( out1_grants == 3'b001 && out1_domain == 1'b1 ) begin
			if ( in0_cur_domain == 1'b1 )
				in0_grants_m = 3'b100;
			if ( in_ter_cur_domain == 1'b1 )
				in_ter_grants_m[2] = 1'b0;
		end

		else if ( out1_grants == 3'b010 && out1_domain == 1'b0 ) begin
			in_ter_grants_m = 3'b100;
			in0_grants_m[2] = 1'b0;
		end

		else if ( out1_grants == 3'b010 && out1_domain == 1'b1 ) begin
			if ( in_ter_cur_domain == 1'b1 )
				in_ter_grants_m = 3'b100;
			if ( in0_cur_domain == 1'b1 )
				in0_grants_m[2] = 1'b0;
		end

		else if ( out1_grants == 3'b000 && out1_domain == 1'b0 ) begin
			in0_grants_m[2] = 1'b0;
			in_ter_grants_m[2] = 1'b0;
		end

		else if ( out1_grants == 3'b000 && out1_domain == 1'b1 ) begin
			if ( in0_cur_domain == 1'b1 )
				in0_grants_m[2] = 1'b0;
			if ( in_ter_cur_domain == 1'b1 )
				in_ter_grants_m[2] = 1'b0;
		end
	end

	always @(posedge clk) begin
		in0_grants_m[0] = 1'b0;
		in_ter_grants_m[1] = 1'b0;
		in1_grants_m[2] = 1'b0;
	end

	always @(posedge clk) begin
		in0_grants_m[0] = 1'b0;
		in_ter_grants_m[1] = 1'b0;
		in1_grants_m[2] = 1'b0;
	end

	assign in0_grants = in0_grants_m;
	assign in_ter_grants = in_ter_grants_m;
	assign in1_grants = in1_grants_m;

	assign dest0_d0		= in0_deq_msg_d0[`VC_NET_MSG_DEST_FIELD(p,o,s)];
	assign dest1_d0		= in1_deq_msg_d0[`VC_NET_MSG_DEST_FIELD(p,o,s)];
	assign dest_ter_d0	= in_deq_msg_ter_d0[`VC_NET_MSG_DEST_FIELD(p,o,s)];

	assign dest0_d1		= in0_deq_msg_d1[`VC_NET_MSG_DEST_FIELD(p,o,s)];
	assign dest1_d1		= in1_deq_msg_d1[`VC_NET_MSG_DEST_FIELD(p,o,s)];
	assign dest_ter_d1	= in_deq_msg_ter_d1[`VC_NET_MSG_DEST_FIELD(p,o,s)];


	// Note: to prevent livelocking, the route computation is only done at the
	// terminal input controls, and the other input controls simplely pass the
	// message through
	
	plab4_net_RouterInputCtrl_Arbiter_NOTP
	#(
		.p_router_id				(p_router_id),
		.p_num_routers				(p_num_routers),
		.p_default_reqs				(3'b100)
	)
	in0_ctrl
	(
		.dest_d0					(dest0_d0),
		.dest_d1					(dest0_d1),

		.in_val_d0					(in0_deq_val_d0),
		.in_val_d1					(in0_deq_val_d1),
		.in_rdy_d0					(in0_deq_rdy_d0),
		.in_rdy_d1					(in0_deq_rdy_d1),

		.reqs						(in0_reqs),
		.grants						(in0_grants),

		.cur_domain					(in0_cur_domain)
	);


	// Note: the following is the input terminal control to prevent deadlock
	
	plab4_net_RouterInputTerminalCtrl_Aribter_NOTP
	#(
	  .p_router_id		(p_router_id),
	  .p_num_routers	(p_num_routers),
	  .p_num_free_nbits	(4)
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

	  .cur_domain		(in_ter_cur_domain)
	);

	plab4_net_RouterInputCtrl_Arbiter_NOTP
	#(
	  .p_router_id		(p_router_id),
	  .p_num_routers	(p_num_routers),
	  .p_default_reqs	(3'b001)
	)
	in1_ctrl
	(
	  .dest_d0			(dest1_d0),
	  .dest_d1			(dest1_d1),

	  .in_val_d0		(in1_deq_val_d0),
	  .in_val_d1		(in1_deq_val_d1),
	  .in_rdy_d0		(in1_deq_rdy_d0),
	  .in_rdy_d1		(in1_deq_rdy_d1),

	  .reqs				(in1_reqs),
	  .grants			(in1_grants),

	  .cur_domain		(in1_cur_domain)

	);

	//----------------------------------------------------------------------
	// Output controls
	//----------------------------------------------------------------------

	plab4_net_RouterOutputCtrl out0_ctrl
	(
		.clk			(clk),
		.reset			(reset),

		.out_domain		(out0_domain),

		.reqs			(out0_reqs),
		.grants			(out0_grants),

		.out_val		(out0_val),
		.out_rdy		(out0_rdy),
		.xbar_sel		(xbar_sel0)
	);

	plab4_net_RouterOutputCtrl out_ter_ctrl
	(
		.clk			(clk),
		.reset			(reset),

		.out_domain		(out_ter_domain),

		.reqs			(out_ter_reqs),
		.grants			(out_ter_grants),

		.out_val		(out_ter_val),
		.out_rdy		(out_ter_rdy),
		.xbar_sel		(xbar_sel1)
	);

	plab4_net_RouterOutputCtrl out1_ctrl
	(
		.clk			(clk),
		.reset			(reset),

		.out_domain		(out1_domain),

		.reqs			(out1_reqs),
		.grants			(out1_grants),

		.out_val		(out1_val),
		.out_rdy		(out1_rdy),
		.xbar_sel		(xbar_sel2)
	);

endmodule 
`endif /* PLAB4_NET_ROUTER_BASE_NOTP_NEW_V */
