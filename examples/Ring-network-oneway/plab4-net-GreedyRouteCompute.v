//========================================================================
// Greedy Route Compute
//========================================================================

`ifndef PLAB4_NET_GREEDY_ROUTE_COMPUTE_V
`define PLAB4_NET_GREEDY_ROUTE_COMPUTE_V

`define ROUTE_PREV  2'b00
`define ROUTE_NEXT  2'b01
`define ROUTE_TERM  2'b10

module plab4_net_GreedyRouteCompute
#(
  parameter p_router_id   = 0,
  parameter p_num_routers = 8,

  // parameter not meant to be set outside this module

  parameter c_dest_nbits = $clog2( p_num_routers )
)
(
  input					   {Domain domain} 	domain,
  input [c_dest_nbits-1:0] {Domain domain}	dest,
  output reg [1:0]         {Domain domain}	route
);

  // calculate forward and backward hops

  wire [c_dest_nbits-1:0] {Domain domain}	forw_hops;
  wire [c_dest_nbits-1:0] {Domain domain}	backw_hops;

  assign forw_hops =  ( dest - p_router_id );
  assign backw_hops = ( p_router_id - dest );

  always @(*) begin
    if ( dest == p_router_id )
      route = `ROUTE_TERM;
    else if ( forw_hops < backw_hops )
      route = `ROUTE_NEXT;
    else
      route = `ROUTE_PREV;
  end

endmodule

`endif /* PLAB4_NET_GREEDY_ROUTE_COMPUTE_V */
