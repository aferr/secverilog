//========================================================================
// Verilog Components: Queues
//========================================================================

`ifndef VC_QUEUES_COMPONENT_V
`define VC_QUEUES_COMPONENT_V

`include "vc-regs.v"
`include "vc-muxes.v"
`include "vc-regfiles.v"

//------------------------------------------------------------------------
// Defines
//------------------------------------------------------------------------

`define VC_QUEUE_NORMAL   4'b0000
`define VC_QUEUE_PIPE     4'b0001
`define VC_QUEUE_BYPASS   4'b0010

//------------------------------------------------------------------------
// Multi-Element Queue Control Logic
//------------------------------------------------------------------------
// This is the control logic for a multi-elment queue. It is designed to
// be attached to a Regfile storage element. Additionally, it includes
// the ability to statically enable pipeline and/or bypass behavior.
// Pipeline behavior is when the deq_rdy signal is combinationally wired
// to the enq_rdy signal allowing elements to be dequeued and enqueued in
// the same cycle when the queue is full. Bypass behavior is when the
// enq_val signal is cominationally wired to the deq_val signal allowing
// elements to bypass the storage element if the storage element is
// empty.

module vc_QueueCtrl_ter
#(
  parameter p_type     = `VC_QUEUE_NORMAL,
  parameter p_num_msgs = 2,

  // Local constants not meant to be set from outside the module
  parameter c_addr_nbits = $clog2(p_num_msgs)
)(
  input                     {L}				clk, reset,

  input						{L}				domain,

  input                     {Domain domain}	enq_val,        // Enqueue data is valid
  output                    {Domain domain}	enq_rdy,        // Ready for producer to enqueue

  output                    {Domain domain}	deq_val,        // Dequeue data is valid
  input                     {Domain domain}	deq_rdy,        // Consumer is ready to dequeue

  output                    {Domain domain}	write_en,       // Wen to wire to regfile
  output [c_addr_nbits-1:0] {Domain domain}	write_addr,     // Waddr to wire to regfile
  output [c_addr_nbits-1:0] {Domain domain}	read_addr,      // Raddr to wire to regfile
  output                    {Domain domain}	bypass_mux_sel, // Control mux for bypass queues
  output [c_addr_nbits:0]   {Domain domain}	num_free_entries // Num of free entries in queue
);

  wire [c_addr_nbits-1:0] 	{Domain domain}	enq_ptr;
  wire [c_addr_nbits-1:0] 	{Domain domain}	enq_ptr_next;

  vc_ResetReg#(c_addr_nbits) enq_ptr_reg
  (
    .clk     (clk),
    .reset   (reset),
	.domain	 (domain),
    .d       (enq_ptr_next),
    .q       (enq_ptr)
  );

  wire [c_addr_nbits-1:0] 	{Domain domain}	deq_ptr;
  wire [c_addr_nbits-1:0] 	{Domain domain}	deq_ptr_next;

  vc_ResetReg#(c_addr_nbits) deq_ptr_reg
  (
    .clk   (clk),
    .reset (reset),
	.domain(domain),
    .d     (deq_ptr_next),
    .q     (deq_ptr)
  );

  assign write_addr = enq_ptr;
  assign read_addr  = deq_ptr;

  // Extra state to tell difference between full and empty

  wire 						{Domain domain}	full;
  wire 						{Domain domain}	full_next;

  vc_ResetReg#(1) full_reg
  (
    .clk   (clk),
    .reset (reset),
	.domain(domain),
    .d     (full_next),
    .q     (full)
  );

  // Determine if pipeline or bypass behavior is enabled

  wire	{Domain domain}	 c_pipe_en   = |( p_type & `VC_QUEUE_PIPE   );
  wire  {Domain domain}	 c_bypass_en = |( p_type & `VC_QUEUE_BYPASS );

  // We enq/deq only when they are both ready and valid

  wire {Domain domain}	do_enq = enq_rdy && enq_val;
  wire {Domain domain}	do_deq = deq_rdy && deq_val;

  // Determine if we have pipeline or bypass behaviour and
  // set the write enable accordingly.

  wire {Domain domain} empty     = ~full && (enq_ptr == deq_ptr);
  wire {Domain domain} do_pipe   = c_pipe_en   && full  && do_enq && do_deq;
  wire {Domain domain} do_bypass = c_bypass_en && empty && do_enq && do_deq;

  assign write_en = do_enq && ~do_bypass;

  // Regardless of the type of queue or whether or not we are actually
  // doing a bypass, if the queue is empty then we select the enq bits,
  // otherwise we select the output of the queue state elements.

  assign bypass_mux_sel = empty;

  // Ready signals are calculated from full register. If pipeline
  // behavior is enabled, then the enq_rdy signal is also calculated
  // combinationally from the deq_rdy signal. If bypass behavior is
  // enabled then the deq_val signal is also calculated combinationally
  // from the enq_val signal.

  assign enq_rdy  = ~full  || ( c_pipe_en   && full  && deq_rdy );
  assign deq_val  = ~empty || ( c_bypass_en && empty && enq_val );

  // Control logic for the enq/deq pointers and full register

  wire [c_addr_nbits-1:0] {Domain domain} deq_ptr_plus1 = deq_ptr + 1'b1;
  wire [c_addr_nbits-1:0] {Domain domain} deq_ptr_inc
    = (deq_ptr_plus1 == p_num_msgs) ? {c_addr_nbits{1'b0}} : deq_ptr_plus1;

  wire [c_addr_nbits-1:0] {Domain domain} enq_ptr_plus1 = enq_ptr + 1'b1;
  wire [c_addr_nbits-1:0] {Domain domain} enq_ptr_inc
    = (enq_ptr_plus1 == p_num_msgs) ? {c_addr_nbits{1'b0}} : enq_ptr_plus1;

  assign deq_ptr_next
    = ( do_deq && ~do_bypass ) ? ( deq_ptr_inc ) : deq_ptr;

  assign enq_ptr_next
    = ( do_enq && ~do_bypass ) ? ( enq_ptr_inc ) : enq_ptr;

  assign full_next
    = ( do_enq && ~do_deq && ( enq_ptr_inc == deq_ptr ) ) ? 1'b1
    : ( do_deq && full && ~do_pipe )                      ? 1'b0
    :                                                       full;

  // Number of free entries

  assign num_free_entries
    = full                ? {(c_addr_nbits+1){1'b0}}
    : empty               ? p_num_msgs[c_addr_nbits:0]
    : (enq_ptr > deq_ptr) ? p_num_msgs[c_addr_nbits:0] - (enq_ptr - deq_ptr)
    : (deq_ptr > enq_ptr) ? deq_ptr - enq_ptr
    :                       {(c_addr_nbits+1){1'bx}};

endmodule
//------------------------------------------------------------------------
// Multi-Element Queue Control Logic
//------------------------------------------------------------------------
// This is the control logic for a multi-elment queue. It is designed to
// be attached to a Regfile storage element. Additionally, it includes
// the ability to statically enable pipeline and/or bypass behavior.
// Pipeline behavior is when the deq_rdy signal is combinationally wired
// to the enq_rdy signal allowing elements to be dequeued and enqueued in
// the same cycle when the queue is full. Bypass behavior is when the
// enq_val signal is cominationally wired to the deq_val signal allowing
// elements to bypass the storage element if the storage element is
// empty.

module vc_QueueCtrl
#(
  parameter p_type     = `VC_QUEUE_NORMAL,
  parameter p_num_msgs = 2,

  // Local constants not meant to be set from outside the module
  parameter c_addr_nbits = $clog2(p_num_msgs)
)(
  input                     {L}				clk, reset,

  input						{L}				domain,
  input						{L}				domain_signal,

  input                     {Domain domain_signal}	enq_val,        // Enqueue data is valid
  output                    {Domain domain}	enq_rdy,        // Ready for producer to enqueue

  output                    {Domain domain}	deq_val,        // Dequeue data is valid
  input                     {Domain domain}	deq_rdy,        // Consumer is ready to dequeue

  output                    {Domain domain}	write_en,       // Wen to wire to regfile
  output [c_addr_nbits-1:0] {Domain domain}	write_addr,     // Waddr to wire to regfile
  output [c_addr_nbits-1:0] {Domain domain}	read_addr,      // Raddr to wire to regfile
  output                    {Domain domain}	bypass_mux_sel, // Control mux for bypass queues
  output [c_addr_nbits:0]   {Domain domain}	num_free_entries // Num of free entries in queue
);

  wire						{Domain domain}	enq_rdy_m;
  reg						{Domain domain}	enq_rdy;
  // Enqueue and dequeue pointers
  always @(*) begin
 	if ( domain == 1'b0 )
		enq_rdy = enq_rdy_m & (~domain_signal);
	else
		enq_rdy = enq_rdy_m & (domain_signal);
  end

  wire [c_addr_nbits-1:0] 	{Domain domain}	enq_ptr;
  wire [c_addr_nbits-1:0] 	{Domain domain}	enq_ptr_next;

  vc_ResetReg#(c_addr_nbits) enq_ptr_reg
  (
    .clk     (clk),
    .reset   (reset),
	.domain	 (domain),
    .d       (enq_ptr_next),
    .q       (enq_ptr)
  );

  wire [c_addr_nbits-1:0] 	{Domain domain}	deq_ptr;
  wire [c_addr_nbits-1:0] 	{Domain domain}	deq_ptr_next;

  vc_ResetReg#(c_addr_nbits) deq_ptr_reg
  (
    .clk   (clk),
    .reset (reset),
	.domain(domain),
    .d     (deq_ptr_next),
    .q     (deq_ptr)
  );

  assign write_addr = enq_ptr;
  assign read_addr  = deq_ptr;

  // Extra state to tell difference between full and empty

  wire 						{Domain domain}	full;
  wire 						{Domain domain}	full_next;

  vc_ResetReg#(1) full_reg
  (
    .clk   (clk),
    .reset (reset),
	.domain(domain),
    .d     (full_next),
    .q     (full)
  );

  // Determine if pipeline or bypass behavior is enabled

  wire {Domain domain}	 c_pipe_en   = |( p_type & `VC_QUEUE_PIPE   );
  wire {Domain domain}	 c_bypass_en = |( p_type & `VC_QUEUE_BYPASS );

  // We enq/deq only when they are both ready and valid

  wire {Domain domain}	do_enq ;
  always @(*) begin
  	if ( domain == 1'b0 && domain_signal == 1'b0 )
		do_enq <= enq_rdy & enq_val;
	else if ( domain == 1'b1 && domain_signal == 1'b1 )
		do_enq <= enq_rdy & enq_val;
	else
		do_enq <= 1'b0;
  end

  wire {Domain domain}	do_deq = deq_rdy && deq_val;

  // Determine if we have pipeline or bypass behaviour and
  // set the write enable accordingly.

  wire {Domain domain} empty     = ~full && (enq_ptr == deq_ptr);
  wire {Domain domain} do_pipe   = c_pipe_en   && full  && do_enq && do_deq;
  wire {Domain domain} do_bypass = c_bypass_en && empty && do_enq && do_deq;

  assign write_en = do_enq && ~do_bypass;

  // Regardless of the type of queue or whether or not we are actually
  // doing a bypass, if the queue is empty then we select the enq bits,
  // otherwise we select the output of the queue state elements.

  assign bypass_mux_sel = empty;

  // Ready signals are calculated from full register. If pipeline
  // behavior is enabled, then the enq_rdy signal is also calculated
  // combinationally from the deq_rdy signal. If bypass behavior is
  // enabled then the deq_val signal is also calculated combinationally
  // from the enq_val signal.

  assign enq_rdy_m  = ~full  || ( c_pipe_en   && full  && deq_rdy );
  
  always @(*) begin
  	if ( domain == 1'b0 && domain_signal == 1'b0)
   		deq_val  <= ~empty || ( c_bypass_en && empty && enq_val );
	else if ( domain == 1'b1 && domain_signal == 1'b1 )
		deq_val  <= ~empty || ( c_bypass_en && empty && enq_val );
	else
		deq_val = 1'b0;
  end
  // Control logic for the enq/deq pointers and full register

  wire [c_addr_nbits-1:0] {Domain domain} deq_ptr_plus1 = deq_ptr + 1'b1;
  wire [c_addr_nbits-1:0] {Domain domain} deq_ptr_inc
    = (deq_ptr_plus1 == p_num_msgs) ? {c_addr_nbits{1'b0}} : deq_ptr_plus1;

  wire [c_addr_nbits-1:0] {Domain domain} enq_ptr_plus1 = enq_ptr + 1'b1;
  wire [c_addr_nbits-1:0] {Domain domain} enq_ptr_inc
    = (enq_ptr_plus1 == p_num_msgs) ? {c_addr_nbits{1'b0}} : enq_ptr_plus1;

  assign deq_ptr_next
    = ( do_deq && ~do_bypass ) ? ( deq_ptr_inc ) : deq_ptr;

  assign enq_ptr_next
    = ( do_enq && ~do_bypass ) ? ( enq_ptr_inc ) : enq_ptr;

  assign full_next
    = ( do_enq && ~do_deq && ( enq_ptr_inc == deq_ptr ) ) ? 1'b1
    : ( do_deq && full && ~do_pipe )                      ? 1'b0
    :                                                       full;

  // Number of free entries

  assign num_free_entries
    = full                ? {(c_addr_nbits+1){1'b0}}
    : empty               ? p_num_msgs[c_addr_nbits:0]
    : (enq_ptr > deq_ptr) ? p_num_msgs[c_addr_nbits:0] - (enq_ptr - deq_ptr)
    : (deq_ptr > enq_ptr) ? deq_ptr - enq_ptr
    :                       {(c_addr_nbits+1){1'bx}};

endmodule

//------------------------------------------------------------------------
// Multi-Element Queue Datapath
//------------------------------------------------------------------------
// This is the datpath for multi-element queues. It includes a register
// and a bypass mux if needed.

module vc_QueueDpath
#(
  parameter p_type      = `VC_QUEUE_NORMAL,
  parameter p_msg_nbits = 4,
  parameter p_num_msgs  = 2,

  // Local constants not meant to be set from outside the module
  parameter c_addr_nbits = $clog2(p_num_msgs)
)(
  input                     {L}				clk,
  input                     {L}				reset,
  input						{L}				domain,
  input						{L}				domain_signal,
  input                     {Domain domain}	write_en,
  input                     {Domain domain}	bypass_mux_sel,
  input  [c_addr_nbits-1:0] {Domain domain}	write_addr,
  input  [c_addr_nbits-1:0] {Domain domain}	read_addr,
  input   [p_msg_nbits-1:0] {Domain domain_signal}	enq_msg,
  output  [p_msg_nbits-1:0] {Domain domain}	deq_msg
);

  // Queue storage

  wire [p_msg_nbits-1:0] 	{Domain domain}	read_data;
  wire [p_msg_nbits-1:0]	{Domain domain}	enq_msg_domain;
  wire 						{Domain domain} write_en_domain;

  always @(*) begin
  	if ( domain == 1'b0 && domain_signal == 1'b0 ) begin
		enq_msg_domain = enq_msg;
		write_en_domain = write_en;
	end
	else if ( domain == 1'b1 && domain_signal == 1'b1 ) begin
		enq_msg_domain = enq_msg;
		write_en_domain = write_en;
	end
	else begin
		enq_msg_domain = 32'bx;
		write_en_domain = 1'b0;
	end
  end
	

  vc_Regfile_1r1w#(p_msg_nbits,p_num_msgs) qstore
  (
    .clk        (clk),
    .reset      (reset),
	.domain		(domain),
    .read_addr  (read_addr),
    .read_data  (read_data),
    .write_en   (write_en),
    .write_addr (write_addr),
    .write_data (enq_msg_domain)
  );

  // Bypass muxing

  generate
  if ( |(p_type & `VC_QUEUE_BYPASS ) )

    vc_Mux2#(p_msg_nbits) bypass_mux
    (
      .in0 (read_data),
      .in1 (enq_msg_domain),
	  .domain(domain),
      .sel (bypass_mux_sel),
      .out (deq_msg)
    );

  else
    assign deq_msg = read_data;
  endgenerate

endmodule
`endif /* VC_QUEUES_COMPONENT_V */
