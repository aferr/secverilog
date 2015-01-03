//========================================================================
// Verilog Components: Arbiters
//========================================================================
// There are three basic arbiter components which are provided in this
// file: vc_FixedArbChain, vc_VariableArbChain, vc_RoundRobinArbChain.
// These basic components can be combined in various ways to create the
// desired arbiter.

`ifndef VC_ARBITERS_V
`define VC_ARBITERS_V

`include "vc-regs.v"

//------------------------------------------------------------------------
// vc_FixedArb
//------------------------------------------------------------------------
// reqs[0] has the highest priority, reqs[1] has the second highest
// priority, etc.

module vc_FixedArb
#(
  parameter p_num_reqs = 2
)(
  input  [p_num_reqs-1:0] reqs,  // 1 = making a req, 0 = no req
  output [p_num_reqs-1:0] grants // (one-hot) 1 = which req won grant
);

  wire dummy_kout;

  vc_FixedArbChain#(p_num_reqs) fixed_arb_chain
  (
    .kin    (1'b0),
    .reqs   (reqs),
    .grants (grants),
    .kout   (dummy_kout)
  );

endmodule

//------------------------------------------------------------------------
// vc_VariableArb
//------------------------------------------------------------------------
// The input priority signal is a one-hot signal where the one indicates
// which request should be given highest priority.

module vc_VariableArb
#(
  parameter p_num_reqs = 2
)(
  input					  {L}				domain,
  input  [p_num_reqs-1:0] {Domain domain}	priority,  // (one-hot) 1 is req w/ highest pri
  input  [p_num_reqs-1:0] {Domain domain}	reqs,      // 1 = making a req, 0 = no req
  output [p_num_reqs-1:0] {Domain domain}	grants     // (one-hot) 1 is req won grant
);

  wire {Domain domain}	dummy_kout;

  vc_VariableArbChain#(p_num_reqs) variable_arb_chain
  (
  	.domain	  (domain),
    .kin      (1'b0),
    .priority (priority),
    .reqs     (reqs),
    .grants   (grants),
    .kout     (dummy_kout)
  );

endmodule

//------------------------------------------------------------------------
// vc_RoundRobinArbChain
//------------------------------------------------------------------------
// Ensures strong fairness among the requesters. The requester which wins
// the grant will be the lowest priority requester the next cycle.

module vc_RoundRobinArbChain
#(
  parameter p_num_reqs             = 2,
  parameter p_priority_reset_value = 1  // (one-hot) 1 = high priority req
)(
  input                   {L}				clk,
  input                   {L}				reset,
  input					  {L}				domain,
  input                   {Domain domain}	kin,    // kill in
  input  [p_num_reqs-1:0] {Domain domain}	reqs,   // 1 = making a req, 0 = no req
  output [p_num_reqs-1:0] {Domain domain}	grants, // (one-hot) 1 is req won grant
  output                  {Domain domain}	kout    // kill out
);

  // We only update the priority if a requester actually received a grant

  wire	{Domain domain}	priority_en = |grants;

  // Next priority is just the one-hot grant vector left rotated by one

  wire [p_num_reqs-1:0]	{Domain domain}	priority_next
    = { grants[p_num_reqs-2:0], grants[p_num_reqs-1] };

  // State for the one-hot priority vector

  wire [p_num_reqs-1:0]	{Domain domain}	priority;

  vc_EnResetReg#(p_num_reqs,p_priority_reset_value) priority_reg
  (
    .clk   (clk),
    .reset (reset),
	.domain(domain),
    .en    (priority_en),
    .d     (priority_next),
    .q     (priority)
  );

  // Variable arbiter chain

  vc_VariableArbChain#(p_num_reqs) variable_arb_chain
  (
    .kin      (kin),
    .priority (priority),
    .reqs     (reqs),
    .grants   (grants),
    .kout     (kout)
  );

endmodule

//------------------------------------------------------------------------
// vc_RoundRobinArb
//------------------------------------------------------------------------
// Ensures strong fairness among the requesters. The requester which wins
// the grant will be the lowest priority requester the next cycle.
//
//  NOTE : Ideally we would just instantiate the vc_RoundRobinArbChain
//         and wire up kin to zero, but VCS seems to have trouble with
//         correctly elaborating the parameteres in that situation. So
//         for now we just duplicate the code from vc_RoundRobinArbChain
//

module vc_RoundRobinArb #( parameter p_num_reqs = 2 )
(
  input                   {L}				clk,
  input                   {L}				reset,
  input					  {L}				domain,
  input  [p_num_reqs-1:0] {Domain domain}	reqs,    // 1 = making a req, 0 = no req
  output [p_num_reqs-1:0] {Domain domain}	grants   // (one-hot) 1 is req won grant
);

  // We only update the priority if a requester actually received a grant

  wire {Domain domain}	priority_en = |grants;

  // Next priority is just the one-hot grant vector left rotated by one

  wire [p_num_reqs-1:0] {Domain domain}	priority_next
    = { grants[p_num_reqs-2:0], grants[p_num_reqs-1] };

  // State for the one-hot priority vector

  wire [p_num_reqs-1:0] {Domain domain}	priority;

  vc_EnResetReg#(p_num_reqs,1) priority_reg
  (
    .clk   (clk),
    .reset (reset),
	.domain(domain),
    .en    (priority_en),
    .d     (priority_next),
    .q     (priority)
  );

  // Variable arbiter chain

  wire {Domain domain}	dummy_kout;

  vc_VariableArbChain#(p_num_reqs) variable_arb_chain
  (
  	.domain	  (domain),
    .kin      (1'b0),
    .priority (priority),
    .reqs     (reqs),
    .grants   (grants),
    .kout     (dummy_kout)
  );

endmodule

`endif /* VC_ARBITERS_V */

