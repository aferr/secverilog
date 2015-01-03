//========================================================================
// Router Input Ctrl Without Timing Channel Protection
//========================================================================

`ifndef	PLAB4_NET_ROUTER_INPUT_CTRL_NOTP_V
`define	PLAB4_NET_ROUTER_INPUT_CTRL_NOTP_V

module	plab4_net_RouterInputCtrl_NOTP
#(
	parameter p_router_id		= 0,
	parameter p_num_routers		= 8,

	parameter p_default_reqs	= 3'b001,

	parameter c_dest_nbits		= $clog2( p_num_routers )

	//parameter domain			= 0
)
(
	input						{Domain domain_ID}	domain_ID,

	input	[c_dest_nbits-1:0]	{Domain domain_ID}	dest,

	input						{Domain domain_ID}	in_val,
	output						{Domain domain_ID}	in_rdy,


	output	[2:0]				{Domain domain_ID}	reqs,
	input	[2:0]				{Domain domain_ID}	grants
);

	assign in_rdy = | (reqs & grants);

	reg	[2:0]					{Domain domain_ID}	reqs;

	always @(*)	begin
		if (in_val) begin

			if ( dest == p_router_id )
				reqs = 3'b010;

			else
				reqs = p_default_reqs;
		end
		else begin
			reqs = 3'b000;
		end
	end

endmodule

`endif /* PLAB4_NET_ROUTER_INPUT_CTRL_NOTP_V */
