//========================================================================
// Verilog Components: Queues
//========================================================================

`ifndef VC_QUEUES_V
`define VC_QUEUES_V

`include "vc-regs.v"
`include "vc-muxes.v"
`include "vc-regfiles.v"
`include "vc-queues-component.v"

//------------------------------------------------------------------------
// Defines
//------------------------------------------------------------------------

`define VC_QUEUE_NORMAL   4'b0000
`define VC_QUEUE_PIPE     4'b0001
`define VC_QUEUE_BYPASS   4'b0010

//------------------------------------------------------------------------
// Queue
//------------------------------------------------------------------------

module vc_Queue
#(
  parameter p_type      = `VC_QUEUE_NORMAL,
  parameter p_msg_nbits = 1,
  parameter p_num_msgs  = 2,

  // indicate the domain it belongs to
  //parameter domain		= 1'b0,

  // parameters not meant to be set outside this module
  parameter c_addr_nbits = $clog2(p_num_msgs)
)(
  input                    {L}						clk,
  input                    {L}						reset,

  input					   {L}						domain,
  input					   {L}						domain_signal,

  input                    {Domain domain_signal}	enq_val,
  output                   {Domain domain}			enq_rdy,
  input  [p_msg_nbits-1:0] {Domain domain_signal}	enq_msg,

  output                   {Domain domain}			deq_val,
  input                    {Domain domain}			deq_rdy,
  output [p_msg_nbits-1:0] {Domain domain}			deq_msg,

  output [c_addr_nbits:0]  {Domain domain}			num_free_entries
);


  generate
  begin

    wire {Domain domain}     				write_en;
    wire {Domain domain}	 				bypass_mux_sel;
    wire [c_addr_nbits-1:0] {Domain domain}	write_addr;
    wire [c_addr_nbits-1:0] {Domain domain}	read_addr;

    vc_QueueCtrl#(p_type,p_num_msgs) ctrl
    (
      .clk              (clk),
      .reset            (reset),
	  .domain			(domain),
	  .domain_signal	(domain_signal),
      .enq_val          (enq_val),
      .enq_rdy          (enq_rdy),
      .deq_val          (deq_val),
      .deq_rdy          (deq_rdy),
      .write_en         (write_en),
      .write_addr       (write_addr),
      .read_addr        (read_addr),
      .bypass_mux_sel   (bypass_mux_sel),
      .num_free_entries (num_free_entries)
    );

    vc_QueueDpath#(p_type,p_msg_nbits,p_num_msgs) dpath
    (
      .clk              (clk),
      .reset            (reset),
	  .domain			(domain),
	  .domain_signal	(domain_signal),
      .write_en         (write_en),
      .bypass_mux_sel   (bypass_mux_sel),
      .write_addr       (write_addr),
      .read_addr        (read_addr),
      .enq_msg          (enq_msg),
      .deq_msg          (deq_msg)
    );

  end
  endgenerate

  // Assertions

  always @( posedge clk ) begin
    if ( !reset ) begin
      `VC_ASSERT_NOT_X( enq_val );
      `VC_ASSERT_NOT_X( enq_rdy );
      `VC_ASSERT_NOT_X( deq_val );
      `VC_ASSERT_NOT_X( deq_rdy );
    end
  end

endmodule

//------------------------------------------------------------------------
// Queue
//------------------------------------------------------------------------

module vc_Queue_ter
#(
  parameter p_type      = `VC_QUEUE_NORMAL,
  parameter p_msg_nbits = 1,
  parameter p_num_msgs  = 2,

  // indicate the domain it belongs to
  //parameter domain		= 1'b0,

  // parameters not meant to be set outside this module
  parameter c_addr_nbits = $clog2(p_num_msgs)
)(
  input                    {L}						clk,
  input                    {L}						reset,

  input					   {L}						domain,

  input                    {Domain domain}			enq_val,
  output                   {Domain domain}			enq_rdy,
  input  [p_msg_nbits-1:0] {Domain domain}			enq_msg,

  output                   {Domain domain}			deq_val,
  input                    {Domain domain}			deq_rdy,
  output [p_msg_nbits-1:0] {Domain domain}			deq_msg,

  output [c_addr_nbits:0]  {Domain domain}			num_free_entries
);


  generate
  begin

    wire {Domain domain}     				write_en;
    wire {Domain domain}	 				bypass_mux_sel;
    wire [c_addr_nbits-1:0] {Domain domain}	write_addr;
    wire [c_addr_nbits-1:0] {Domain domain}	read_addr;

    vc_QueueCtrl_ter#(p_type,p_num_msgs) ctrl
    (
      .clk              (clk),
      .reset            (reset),
	  .domain			(domain),
      .enq_val          (enq_val),
      .enq_rdy          (enq_rdy),
      .deq_val          (deq_val),
      .deq_rdy          (deq_rdy),
      .write_en         (write_en),
      .write_addr       (write_addr),
      .read_addr        (read_addr),
      .bypass_mux_sel   (bypass_mux_sel),
      .num_free_entries (num_free_entries)
    );

    vc_QueueDpath#(p_type,p_msg_nbits,p_num_msgs) dpath
    (
      .clk              (clk),
      .reset            (reset),
	  .domain			(domain),
	  .domain_signal	(domain),
      .write_en         (write_en),
      .bypass_mux_sel   (bypass_mux_sel),
      .write_addr       (write_addr),
      .read_addr        (read_addr),
      .enq_msg          (enq_msg),
      .deq_msg          (deq_msg)
    );

  end
  endgenerate

  // Assertions

  always @( posedge clk ) begin
    if ( !reset ) begin
      `VC_ASSERT_NOT_X( enq_val );
      `VC_ASSERT_NOT_X( enq_rdy );
      `VC_ASSERT_NOT_X( deq_val );
      `VC_ASSERT_NOT_X( deq_rdy );
    end
  end

endmodule
`endif /* VC_QUEUES_V */

