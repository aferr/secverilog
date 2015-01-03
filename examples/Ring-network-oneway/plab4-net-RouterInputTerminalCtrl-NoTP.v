//========================================================================
// Router Input Terminal Ctrl Without Timing Channel Protection
//========================================================================

`ifndef PLAB4_NET_ROUTER_INPUT_TERMINAL_CTRL_NOTP_V
`define	PLAB4_NET_ROUTER_INPUT_TERMINAL_CTRL_NOTP_V

`include "plab4-net-GreedyRouteCompute.v"

module plab4_net_RouterInputTerminalCtrl_NOTP
#(
	parameter p_router_id			= 0,
	parameter p_num_routers			= 8,
	parameter p_num_free_nbits		= 2,

	parameter c_dest_nbits			= $clog2(p_num_routers)
)
(
	input							{Domain domain_ID}	domain_ID,
	input	[c_dest_nbits-1:0]		{Domain domain_ID}	dest,

	input							{Domain domain_ID}	in_val,
	output							{Domain domain_ID}	in_rdy,

	input	[p_num_free_nbits-1:0]	{Domain domain_ID}	num_free_west,
	input	[p_num_free_nbits-1:0]	{Domain domain_ID}	num_free_east,

	output	[2:0]					{Domain domain_ID}	reqs,
	input	[2:0]					{Domain domain_ID}	grants
);

	wire	[1:0]					{Domain domain_ID}	route;

	plab4_net_GreedyRouteCompute
	#(
		.p_router_id				(p_router_id),
		.p_num_routers				(p_num_routers)
	)
	route_compute
	(
		.domain						(domain_ID),
		.dest						(dest),
		.route						(route)
	);

	assign in_rdy = | (reqs &  grants);

	reg		[2:0]					{Domain domain_ID}	reqs;

	always @(*) begin
		if (in_val) begin

			case (route)
				`ROUTE_PREV:	reqs = (num_free_east > 1) ? 3'b001 : 3'b000;
				`ROUTE_TERM:	reqs = 3'b010;
				`ROUTE_NEXT:	reqs = (num_free_west > 1) ? 3'b100 : 3'b000;
			endcase
		end
		else begin
			reqs = 3'b000;
		end
	end

endmodule

`endif /* PLAB4_NET_ROUTER_INPUT_TERMINAL_CTRL_NOTP_V */
