//========================================================================
// Router Input Ctrl Arbiter
//========================================================================

`ifndef PLAB4_NET_ROUTER_INPUT_CTRL_ARBITER_NOTP_V
`define	PLAB4_NET_ROUTER_INPUT_CTRL_ARBITER_NOTP_V

`include "plab4-net-RouterInputCtrl-NoTP.v"

module plab4_net_RouterInputCtrl_Arbiter_NOTP
#(
	parameter p_router_id			= 0,
	parameter p_num_routers			= 8,

	parameter p_default_reqs		= 3'b001,

	parameter c_dest_nbits			= $clog2(p_num_routers)
)
(
	input	[c_dest_nbits-1:0]		{D1}				dest_d0,
	input	[c_dest_nbits-1:0]		{D2}				dest_d1,

	input							{D1}				in_val_d0,
	input							{D2}				in_val_d1,
	output							{D1}				in_rdy_d0,
	output							{D2}				in_rdy_d1,

	output	[2:0]					{Domain cur_domain}	reqs,
	input	[2:0]					{Domain cur_domain}	grants,
	output							{D1}				cur_domain
);

	wire	[2:0]					{D1}				reqs_d0;
	wire	[2:0]					{D2}				reqs_d1;
	reg		[2:0]					{Domain cur_domain}	reqs;
	reg		[2:0]					{D1}				grants_d0;
	reg		[2:0]					{D2}				grants_d1;
	reg								{D1}				cur_domain;

	plab4_net_RouterInputCtrl_NOTP
	#(
		.p_router_id				(p_router_id),
		.p_num_routers				(p_num_routers),
		.p_default_reqs				(p_default_reqs)
	)
	in_d0_ctrl
	(
		.domain_ID					(1'b0),
		.dest						(dest_d0),
		.in_val						(in_val_d0),
		.in_rdy						(in_rdy_d0),
		.reqs						(reqs_d0),
		.grants						(grants_d0)
	);

	plab4_net_RouterInputCtrl_NOTP
	#(
		.p_router_id				(p_router_id),
		.p_num_routers				(p_num_routers),
		.p_default_reqs				(p_default_reqs)
	)
	in_d1_ctrl
	(
		.domain_ID					(1'b1),
		.dest						(dest_d1),
		.in_val						(in_val_d1),
		.in_rdy						(in_rdy_d1),
		.reqs						(reqs_d1),
		.grants						(grants_d1)
	);

	always @(*) begin
		if (reqs_d0 != 3'b000 )
			cur_domain = 1'b0;
		else
			cur_domain = 1'b1;
	end

	always @(*) begin
		if ( cur_domain == 1'b0 ) begin
			reqs = reqs_d0;
			grants_d0 = grants;
			grants_d1 = 3'b000;
		end
		else if ( cur_domain == 1'b1 ) begin
			reqs = reqs_d1;
			//grants_d0 = 3'b000;
			grants_d1 = grants;
		end
	end

endmodule

`endif /* PLAB4_NET_ROUTER_INPUT_CTRL_ARBITER_NOTP_V */
