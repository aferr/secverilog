//========================================================================
// Router Input Ctrl Arbiter With Timing Channel Protection
//========================================================================

`ifndef PLAB4_NET_ROUTER_INPUT_CTRL_ARBITER_TP_V
`define	PLAB4_NET_ROUTER_INPUT_CTRL_ARBITER_TP_V

`include "plab4-net-RouterInputCtrl-new-TP.v"

module plab4_net_RouterInputCtrl_Arbiter_New_TP
#(
	parameter p_router_id			= 0,
	parameter p_num_routers			= 8,

	// indicates the reqs signal to pass through a message
	parameter p_default_reqs		= 3'b001,

	// parameter not meant to be set outside this module
	
	parameter c_dest_nbits			= $clog2 ( p_num_routers )
)
(
	input	[c_dest_nbits-1:0]		{D1}			dest_d0,
	input	[c_dest_nbits-1:0]		{D2}			dest_d1,

	input							{D1}			in_val_d0,
	input							{D2}			in_val_d1,
	output							{D1}			in_rdy_d0,
	output							{D2}			in_rdy_d1,

	output	[2:0]					{Domain domain}	reqs,
	input	[2:0]					{Domain domain}	grants,

	input							{L}				domain
);

  //----------------------------------------------------------------------
  // Combinational logic
  //----------------------------------------------------------------------
	wire	[2:0]					{D1}			reqs_d0;
	wire	[2:0]					{D2}			reqs_d1;
	reg		[2:0]					{Domain domain}	reqs;
	wire	[2:0]					{D1}			grants_d0;
	wire	[2:0]					{D2}			grants_d1;

	plab4_net_RouterInputCtrl_new_TP
	#(
		.p_router_id				(p_router_id),
		.p_num_routers				(p_num_routers),
		.p_default_reqs				(p_default_reqs),
		.domain_ID					(1'b0)
	)
	in_d0_ctrl
	(
		.dest						(dest_d0),
		.in_val						(in_val_d0),
		.in_rdy						(in_rdy_d0),
		.reqs						(reqs_d0),
		.grants						(grants_d0),
		//.domain_ID					(1'b0),
		.domain						(domain)
	);

	plab4_net_RouterInputCtrl_new_TP
	#(
		.p_router_id				(p_router_id),
		.p_num_routers				(p_num_routers),
		.p_default_reqs				(p_default_reqs),
		.domain_ID					(1'b1)
	)
	in_d1_ctrl
	(
		.dest						(dest_d1),
		.in_val						(in_val_d1),
		.in_rdy						(in_rdy_d1),
		.reqs						(reqs_d1),
		.grants						(grants_d1),
		//.domain_ID					(1'b1),
		.domain						(domain)
	);

	always @(*) begin
		if ( domain == 1'b0 )
			reqs = reqs_d0;
		else if ( domain == 1'b1 )
			reqs = reqs_d1;
	end

	always @(*) begin
		if ( domain == 1'b0 )
			grants_d0 <= grants;
		else if ( domain == 1'b1 )
			grants_d1 <= grants;
	end

endmodule

`endif /* PLAB4_NET_ROUTER_INPUT_CTRL_ARBITER_TP_V */
		
