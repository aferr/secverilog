`ifndef VC_ARBCHAIN_V
`define VC_ARBCHAIN_V

//------------------------------------------------------------------------
// vc_FixedArbChain
//------------------------------------------------------------------------
// reqs[0] has the highest priority, reqs[1] has the second
// highest priority, etc.

module vc_FixedArbChain
#(
  parameter p_num_reqs = 2
)(
  input                   kin,    // kill in
  input  [p_num_reqs-1:0] reqs,   // 1 = making a req, 0 = no req
  output [p_num_reqs-1:0] grants, // (one-hot) 1 indicates req won grant
  output                  kout    // kill out
);

  // The internal kills signals essentially form a kill chain from the
  // highest priority to the lowest priority requester. The highest
  // priority requster (say requester i) which is actually making a
  // request sets the kill signal for the next requester to one (ie
  // kills[i+1]) and then this kill signal is propagated to all lower
  // priority requesters.

  wire [p_num_reqs:0] kills;
  assign kills[0] = 1'b0;

  // The per requester logic first computes the grant signal and then
  // computes the kill signal for the next requester.

  wire [p_num_reqs-1:0] grants_int;

  genvar i;
  generate
  for ( i = 0; i < p_num_reqs; i = i + 1 )
  begin : per_req_logic

    // Grant is true if this requester is not killed and it is actually
    // making a req.

    assign grants_int[i] = !kills[i] && reqs[i];

    // Kill is true if this requester was either killed or it received
    // the grant.

    assign kills[i+1] = kills[i] || grants_int[i];

  end
  endgenerate

  // We AND kin into the grant and kout signals afterwards so that we can
  // begin doing the arbitration before we know kin. This also allows us
  // to build hybrid tree-ripple arbiters out of vc_FixedArbChain
  // components.

  assign grants = grants_int & {p_num_reqs{~kin}};
  assign kout   = kills[p_num_reqs] || kin;

endmodule
//------------------------------------------------------------------------
// vc_VariableArbChain
//------------------------------------------------------------------------
// The input priority signal is a one-hot signal where the one indicates
// which request should be given highest priority.

module vc_VariableArbChain
#(
  parameter p_num_reqs = 2
)(
  input					  {L}				domain,
  input                   {Domain domain}	kin,       // kill in
  input  [p_num_reqs-1:0] {Domain domain}	priority,  // (one-hot) 1 is req w/ highest pri
  input  [p_num_reqs-1:0] {Domain domain}	reqs,      // 1 = making a req, 0 = no req
  output [p_num_reqs-1:0] {Domain domain}	grants,    // (one-hot) 1 is req won grant
  output                  {Domain domain}	kout       // kill out
);

  // The internal kills signals essentially form a kill chain from the
  // highest priority to the lowest priority requester. Unliked the fixed
  // arb, the priority input is used to determine which request has the
  // highest priority. We could use a circular kill chain, but static
  // timing analyzers would probably consider it a combinational loop
  // (which it is) and choke. Instead we replicate the kill chain. See
  // Principles and Practices of Interconnection Networks, Dally +
  // Towles, p354 for more info.

  wire [2*p_num_reqs:0]   {Domain domain}	kills;
  assign kills[0] = 1'b1;

  wire [2*p_num_reqs-1:0] {Domain domain}	priority_int = { {p_num_reqs{1'b0}}, priority };
  wire [2*p_num_reqs-1:0] {Domain domain}	reqs_int     = { reqs, reqs };
  wire [2*p_num_reqs-1:0] {Domain domain}	grants_int;

  // The per requester logic first computes the grant signal and then
  // computes the kill signal for the next requester.

  localparam p_num_reqs_x2 = (p_num_reqs << 1);
  genvar i;
  generate
  for ( i = 0; i < 2*p_num_reqs; i = i + 1 )
  begin : per_req_logic

    // If this is the highest priority requester, then we ignore the
    // input kill signal, otherwise grant is true if this requester is
    // not killed and it is actually making a req.

    assign grants_int[i]
      = priority_int[i] ? reqs_int[i] : (!kills[i] && reqs_int[i]);

    // If this is the highest priority requester, then we ignore the
    // input kill signal, otherwise kill is true if this requester was
    // either killed or it received the grant.

    assign kills[i+1]
      = priority_int[i] ? grants_int[i] : (kills[i] || grants_int[i]);

  end
  endgenerate

  // To calculate final grants we OR the two grants from the replicated
  // kill chain. We also AND in the global kin signal.

  assign grants
    = (grants_int[p_num_reqs-1:0] | grants_int[2*p_num_reqs-1:p_num_reqs])
    & {p_num_reqs{~kin}};

  assign kout = kills[2*p_num_reqs] || kin;

endmodule
`endif /* VC_ARBCHAIN_V */
