//========================================================================
// Tasks for Tracing
//========================================================================
// This file is meant to be included from _within_ a module to bring
// various helper tasks and functions for tracing into scope.

//------------------------------------------------------------------------
// Variables
//------------------------------------------------------------------------

integer _vc_trace_len0;
integer _vc_trace_len1;
integer _vc_trace_idx0;
integer _vc_trace_idx1;

// We can use this constant in the declaration of trace_module

localparam vc_trace_nchars = 512;
localparam vc_trace_nbits  = (512 << 3);

// This is the actual trace storage used when displaying a trace

reg [vc_trace_nbits-1:0] _vc_trace_storage;

// No prefix since meant to be accesible from outside module

integer trace_cycles_next = 0;
integer trace_cycles      = 0;

//------------------------------------------------------------------------
// Macros to determine number of characters for a net
//------------------------------------------------------------------------

`ifndef VC_TRACE_TASKS_V
`define VC_TRACE_TASKS_V

`define VC_TRACE_NBITS_TO_NCHARS( nbits_ ) ((nbits_+3)/4)

`endif

//------------------------------------------------------------------------
// vc_trace_str
//------------------------------------------------------------------------
// Appends a string to the trace.

task vc_trace_str
(
  inout [vc_trace_nbits-1:0] trace,
  input [vc_trace_nbits-1:0] str
);
begin

  _vc_trace_len0 = 1;
  while ( str[_vc_trace_len0*8+:8] != 0 ) begin
    _vc_trace_len0 = _vc_trace_len0 + 1;
  end

  _vc_trace_idx0 = trace[15:0];

  for ( _vc_trace_idx1 = _vc_trace_len0-1;
        _vc_trace_idx1 >= 0;
        _vc_trace_idx1 = _vc_trace_idx1 - 1 )
  begin
    trace[ _vc_trace_idx0*8 +: 8 ] = str[ _vc_trace_idx1*8 +: 8 ];
    _vc_trace_idx0 = _vc_trace_idx0 - 1;
  end

  trace[15:0] = _vc_trace_idx0;

end
endtask

//------------------------------------------------------------------------
// vc_trace_str_ljust
//------------------------------------------------------------------------
// Appends a left-justified string to the trace.

task vc_trace_str_ljust
(
  inout [vc_trace_nbits-1:0] trace,
  input [vc_trace_nbits-1:0] str
);
begin

  _vc_trace_idx0 = trace[15:0];
  _vc_trace_idx1 = vc_trace_nchars;

  while ( str[ _vc_trace_idx1*8-1 -: 8 ] != 0 ) begin
    trace[ _vc_trace_idx0*8 +: 8 ] = str[ _vc_trace_idx1*8-1 -: 8 ];
    _vc_trace_idx0 = _vc_trace_idx0 - 1;
    _vc_trace_idx1 = _vc_trace_idx1 - 1;
  end

  trace[15:0] = _vc_trace_idx0;

end
endtask

//------------------------------------------------------------------------
// vc_trace_fill
//------------------------------------------------------------------------
// Appends the given number of characters to the trace.

task vc_trace_fill
(
  inout [vc_trace_nbits-1:0] trace,
  input integer              num,
  input                [7:0] char
);
begin

  _vc_trace_idx0 = trace[15:0];

  for ( _vc_trace_idx1 = 0;
        _vc_trace_idx1 < num;
        _vc_trace_idx1 = _vc_trace_idx1 + 1 )
  begin
    trace[_vc_trace_idx0*8+:8] = char;
    _vc_trace_idx0 = _vc_trace_idx0 - 1;
  end

  trace[15:0] = _vc_trace_idx0;

end
endtask

//------------------------------------------------------------------------
// vc_trace_str_val
//------------------------------------------------------------------------
// Append a string modified by val signal.

task vc_trace_str_val
(
  inout [vc_trace_nbits-1:0] trace,
  input                      val,
  input [vc_trace_nbits-1:0] str
);
begin

  _vc_trace_len1 = 0;
  while ( str[_vc_trace_len1*8+:8] != 0 ) begin
    _vc_trace_len1 = _vc_trace_len1 + 1;
  end

  if ( val )
    vc_trace_str( trace, str );
  else if ( !val )
    vc_trace_fill( trace, _vc_trace_len1, " " );
  else begin
    vc_trace_str( trace, "x" );
    vc_trace_fill( trace, _vc_trace_len1-1, " " );
  end

end
endtask

//------------------------------------------------------------------------
// vc_trace_str_val_rdy
//------------------------------------------------------------------------
// Append a string modified by val/rdy signals.

task vc_trace_str_val_rdy
(
  inout [vc_trace_nbits-1:0] trace,
  input                      val,
  input                      rdy,
  input [vc_trace_nbits-1:0] str
);
begin

  _vc_trace_len1 = 0;
  while ( str[_vc_trace_len1*8+:8] != 0 ) begin
    _vc_trace_len1 = _vc_trace_len1 + 1;
  end

  if ( rdy && val ) begin
    vc_trace_str( trace, str );
  end
  else if ( rdy && !val ) begin
    vc_trace_fill( trace, _vc_trace_len1, " " );
  end
  else if ( !rdy && val ) begin
    vc_trace_str( trace, "#" );
    vc_trace_fill( trace, _vc_trace_len1-1, " " );
  end
  else if ( !rdy && !val ) begin
    vc_trace_str( trace, "." );
    vc_trace_fill( trace, _vc_trace_len1-1, " " );
  end
  else begin
    vc_trace_str( trace, "x" );
    vc_trace_fill( trace, _vc_trace_len1-1, " " );
  end

end
endtask

//------------------------------------------------------------------------
// trace_display
//------------------------------------------------------------------------
// Display a trace on standard output.

reg [3:0] _vc_trace_level;

initial begin
  if ( !$value$plusargs( "trace=%d", _vc_trace_level ) ) begin
    _vc_trace_level = 0;
  end
end

always @( posedge clk ) begin
  trace_cycles <= ( reset ) ? 0 : trace_cycles_next;
end

task trace_display;
begin

  if ( _vc_trace_level > 0 ) begin

    // Reset the counter in the trace

    _vc_trace_storage[15:0] = vc_trace_nchars-1;

    // Trace this module

    trace_module( _vc_trace_storage );

    // Output the trace cycle number

    $write( "%4d: ", trace_cycles );

    // Output the trace

    _vc_trace_idx0 = _vc_trace_storage[15:0];
    for ( _vc_trace_idx1 = vc_trace_nchars-1;
          _vc_trace_idx1 > _vc_trace_idx0;
          _vc_trace_idx1 = _vc_trace_idx1 - 1 )
    begin
      $write( "%s", _vc_trace_storage[_vc_trace_idx1*8+:8] );
    end
    $write("\n");

  end

  // Bump the trace cycle counter

  trace_cycles_next = trace_cycles + 1;

end
endtask

