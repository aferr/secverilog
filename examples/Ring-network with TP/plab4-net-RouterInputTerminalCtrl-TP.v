//========================================================================
// Router Input Terminal Ctrl With Timing Channel Protection
//========================================================================

`ifndef PLAB4_NET_ROUTER_INPUT_TERMINAL_CTRL_TP_V
`define PLAB4_NET_ROUTER_INPUT_TERMINAL_CTRL_TP_V

//+++ gen-harness : begin cut ++++++++++++++++++++++++++++++++++++++++++++
`include "plab4-net-GreedyRouteCompute.v"
//+++ gen-harness : end cut ++++++++++++++++++++++++++++++++++++++++++++++

module plab4_net_RouterInputTerminalCtrl_TP
#(
  parameter p_router_id			= 0,
  parameter p_num_routers		= 8,
  parameter p_num_free_nbits	= 2,

  parameter c_dest_nbits		= $clog2( p_num_routers )

  // indicate which domain it belongs to
  //parameter	domain_ID			= 0

)
(
  input	 [c_dest_nbits-1:0]		{Domain domain_ID}	dest,

  input							{Domain domain_ID}	in_val,
  output						{Domain domain_ID}	in_rdy,

  input  [p_num_free_nbits-1:0]	{Domain domain_ID}	num_free_west,
  input	 [p_num_free_nbits-1:0]	{Domain domain_ID}	num_free_east,

  output [2:0]					{Domain domain_ID}	reqs,
  input	 [2:0]					{Domain domain_ID}	grants,

  input							{L}					domain_ID,
  input							{L}					domain
);

 //+++ gen-harness : begin insert +++++++++++++++++++++++++++++++++++++++
// 
//   // add logic here
// 
//   assign in_rdy = 0;
//   assign reqs = 0;
// 
  //+++ gen-harness : end insert +++++++++++++++++++++++++++++++++++++++++

  //+++ gen-harness : begin cut ++++++++++++++++++++++++++++++++++++++++++

  wire [1:0] {Domain domain_ID}	route;

  //----------------------------------------------------------------------
  // Greedy Route Compute
  //----------------------------------------------------------------------

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


  //----------------------------------------------------------------------
  // Combinational logic
  //----------------------------------------------------------------------
  
  reg [2:0]						{Domain domain_ID}	reqs;
  reg							{Domain domain_ID}	in_rdy_me;
  reg							{Domain domain_ID}	in_rdy;

  // Based on the domain signal to determine the ready signal
  always @(*) begin
	
	// if the control unit belong to the domain 0
	if ( domain_ID == 1'b0 ) begin
	  in_rdy_me = | ( reqs & grants );
      in_rdy	= in_rdy_me & (~domain);
	end
	// othersie, it belongs to domain 1
	else begin
	  in_rdy_me = | ( reqs & grants );
	  in_rdy	= in_rdy_me & domain;
	end
  end

  always @(*) begin
	if ( in_val && ( ( domain_ID == 1'b0 && domain == 1'b0 )|| ( domain_ID == 1'b1 && domain == 1'b1)  )) begin
		
	  case (route)
		// the following implements bubble flow control	  
		`ROUTE_PREV:	reqs = (num_free_east > 1) ? 3'b001 : 3'b000;
		`ROUTE_TERM:	reqs = 3'b010;
		`ROUTE_NEXT:	reqs = (num_free_west > 1) ? 3'b100 : 3'b000;

	  endcase
	end
	else begin
	  // if !val, we don't request any output ports
	  reqs = 3'b000;
	end
  end

endmodule

`endif /* PLAB4_NET_ROUTER_INPUT_TERMINAL_CTRL_TP_V */
