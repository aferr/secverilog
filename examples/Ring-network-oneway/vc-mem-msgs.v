//========================================================================
// vc-mem-msgs : Memory Request/Response Messages
//========================================================================
// The memory request/response messages are used to interact with various
// memories. They are parameterized by the number of bits in the address,
// data, and opaque field.

`ifndef VC_MEM_MSGS_V
`define VC_MEM_MSGS_V

//========================================================================
// Memory Request Message
//========================================================================
// Memory request messages can either be for a read or write. Read
// requests include an opaque field, the address, and the number of bytes
// to read, while write requests include an opaque field, the address,
// the number of bytes to write, and the actual data to write.
//
// Message Format:
//
//    4b    p_opaque_nbits  p_addr_nbits       calc   p_data_nbits
//  +------+---------------+------------------+------+------------------+
//  | type | opaque        | addr             | len  | data             |
//  +------+---------------+------------------+------+------------------+
//
// The message type is parameterized by the number of bits in the opaque
// field, address field, and data field. Note that the size of the length
// field is caclulated from the number of bits in the data field, and
// that the length field is expressed in _bytes_. If the value of the
// length field is zero, then the read or write should be for the full
// width of the data field.
//
// For example, if the opaque field is 8 bits, the address is 32 bits and
// the data is also 32 bits, then the message format is as follows:
//
//   77  74 73           66 65              34 33  32 31               0
//  +------+---------------+------------------+------+------------------+
//  | type | opaque        | addr             | len  | data             |
//  +------+---------------+------------------+------+------------------+
//
// The length field is two bits. A length value of one means read or write
// a single byte, a length value of two means read or write two bytes, and
// so on. A length value of zero means read or write all four bytes. Note
// that not all memories will necessarily support any alignment and/or any
// value for the length field.
//
// The opaque field is reserved for use by a specific implementation. All
// memories should guarantee that every response includes the opaque
// field corresponding to the request that generated the response.

//------------------------------------------------------------------------
// Memory Request Message: Message fields ordered from right to left
//------------------------------------------------------------------------
// We use the following short names to make all of these preprocessor
// macros more succinct.

// Data field

`define VC_MEM_REQ_MSG_DATA_NBITS(o_,a_,d_)                             \
  d_

`define VC_MEM_REQ_MSG_DATA_MSB(o_,a_,d_)                               \
  ( `VC_MEM_REQ_MSG_DATA_NBITS(o_,a_,d_) - 1 )

`define VC_MEM_REQ_MSG_DATA_FIELD(o_,a_,d_)                             \
  (`VC_MEM_REQ_MSG_DATA_MSB(o_,a_,d_)):                                 \
  0

// Length field

`define VC_MEM_REQ_MSG_LEN_NBITS(o_,a_,d_)                              \
  ($clog2(d_/8))

`define VC_MEM_REQ_MSG_LEN_MSB(o_,a_,d_)                                \
  (   `VC_MEM_REQ_MSG_DATA_MSB(o_,a_,d_)                                \
    + `VC_MEM_REQ_MSG_LEN_NBITS(o_,a_,d_) )

`define VC_MEM_REQ_MSG_LEN_FIELD(o_,a_,d_)                              \
  (`VC_MEM_REQ_MSG_LEN_MSB(o_,a_,d_)):                                  \
  (`VC_MEM_REQ_MSG_DATA_MSB(o_,a_,d_) + 1)

// Address field

`define VC_MEM_REQ_MSG_ADDR_NBITS(o_,a_,d_)                             \
  a_

`define VC_MEM_REQ_MSG_ADDR_MSB(o_,a_,d_)                               \
  (   `VC_MEM_REQ_MSG_LEN_MSB(o_,a_,d_)                                 \
    + `VC_MEM_REQ_MSG_ADDR_NBITS(o_,a_,d_) )

`define VC_MEM_REQ_MSG_ADDR_FIELD(o_,a_,d_)                             \
  (`VC_MEM_REQ_MSG_ADDR_MSB(o_,a_,d_)):                                 \
  (`VC_MEM_REQ_MSG_LEN_MSB(o_,a_,d_) + 1)

// Opaque field

`define VC_MEM_REQ_MSG_OPAQUE_NBITS(o_,a_,d_)                           \
  o_

`define VC_MEM_REQ_MSG_OPAQUE_MSB(o_,a_,d_)                             \
  (   `VC_MEM_REQ_MSG_ADDR_MSB(o_,a_,d_)                                \
    + `VC_MEM_REQ_MSG_OPAQUE_NBITS(o_,a_,d_) )

`define VC_MEM_REQ_MSG_OPAQUE_FIELD(o_,a_,d_)                           \
  (`VC_MEM_REQ_MSG_OPAQUE_MSB(o_,a_,d_)):                               \
  (`VC_MEM_REQ_MSG_ADDR_MSB(o_,a_,d_) + 1)

// Type field

`define VC_MEM_REQ_MSG_TYPE_NBITS(o_,a_,d_) 3
`define VC_MEM_REQ_MSG_TYPE_READ     3'd0
`define VC_MEM_REQ_MSG_TYPE_WRITE    3'd1

// write no-refill
`define VC_MEM_REQ_MSG_TYPE_WRITE_INIT 3'd2
`define VC_MEM_REQ_MSG_TYPE_AMO_ADD    3'd3
`define VC_MEM_REQ_MSG_TYPE_AMO_AND    3'd4
`define VC_MEM_REQ_MSG_TYPE_AMO_OR     3'd5
`define VC_MEM_REQ_MSG_TYPE_X          3'dx

`define VC_MEM_REQ_MSG_TYPE_MSB(o_,a_,d_)                               \
  (   `VC_MEM_REQ_MSG_OPAQUE_MSB(o_,a_,d_)                              \
    + `VC_MEM_REQ_MSG_TYPE_NBITS(o_,a_,d_) )

`define VC_MEM_REQ_MSG_TYPE_FIELD(o_,a_,d_)                             \
  (`VC_MEM_REQ_MSG_TYPE_MSB(o_,a_,d_)):                                 \
  (`VC_MEM_REQ_MSG_OPAQUE_MSB(o_,a_,d_) + 1)

// Total size of message

`define VC_MEM_REQ_MSG_NBITS(o_,a_,d_)                                  \
  (   `VC_MEM_REQ_MSG_TYPE_NBITS(o_,a_,d_)                              \
    + `VC_MEM_REQ_MSG_OPAQUE_NBITS(o_,a_,d_)                            \
    + `VC_MEM_REQ_MSG_ADDR_NBITS(o_,a_,d_)                              \
    + `VC_MEM_REQ_MSG_LEN_NBITS(o_,a_,d_)                               \
    + `VC_MEM_REQ_MSG_DATA_NBITS(o_,a_,d_) )

//------------------------------------------------------------------------
// Memory Request Message: Pack message
//------------------------------------------------------------------------

module vc_MemReqMsgPack
#(
  parameter p_opaque_nbits = 8,
  parameter p_addr_nbits   = 32,
  parameter p_data_nbits   = 32,

  // Shorter names for message type, not to be set from outside the module
  parameter o = p_opaque_nbits,
  parameter a = p_addr_nbits,
  parameter d = p_data_nbits
)(
  // Input message

  input  [`VC_MEM_REQ_MSG_TYPE_NBITS(o,a,d)-1:0]   type,
  input  [`VC_MEM_REQ_MSG_OPAQUE_NBITS(o,a,d)-1:0] opaque,
  input  [`VC_MEM_REQ_MSG_ADDR_NBITS(o,a,d)-1:0]   addr,
  input  [`VC_MEM_REQ_MSG_LEN_NBITS(o,a,d)-1:0]    len,
  input  [`VC_MEM_REQ_MSG_DATA_NBITS(o,a,d)-1:0]   data,

  // Output bits

  output [`VC_MEM_REQ_MSG_NBITS(o,a,d)-1:0]        msg
);

  assign msg[`VC_MEM_REQ_MSG_TYPE_FIELD(o,a,d)]   = type;
  assign msg[`VC_MEM_REQ_MSG_OPAQUE_FIELD(o,a,d)] = opaque;
  assign msg[`VC_MEM_REQ_MSG_ADDR_FIELD(o,a,d)]   = addr;
  assign msg[`VC_MEM_REQ_MSG_LEN_FIELD(o,a,d)]    = len;
  assign msg[`VC_MEM_REQ_MSG_DATA_FIELD(o,a,d)]   = data;

endmodule

//------------------------------------------------------------------------
// Memory Request Message: Unpack message
//------------------------------------------------------------------------

module vc_MemReqMsgUnpack
#(
  parameter p_opaque_nbits = 8,
  parameter p_addr_nbits   = 32,
  parameter p_data_nbits   = 32,

  // Shorter names for message type, not to be set from outside the module
  parameter o = p_opaque_nbits,
  parameter a = p_addr_nbits,
  parameter d = p_data_nbits
)(

  // Input bits

  input [`VC_MEM_REQ_MSG_NBITS(o,a,d)-1:0]         msg,

  // Output message

  output [`VC_MEM_REQ_MSG_TYPE_NBITS(o,a,d)-1:0]   type,
  output [`VC_MEM_REQ_MSG_OPAQUE_NBITS(o,a,d)-1:0] opaque,
  output [`VC_MEM_REQ_MSG_ADDR_NBITS(o,a,d)-1:0]   addr,
  output [`VC_MEM_REQ_MSG_LEN_NBITS(o,a,d)-1:0]    len,
  output [`VC_MEM_REQ_MSG_DATA_NBITS(o,a,d)-1:0]   data
);

  assign type   = msg[`VC_MEM_REQ_MSG_TYPE_FIELD(o,a,d)];
  assign opaque = msg[`VC_MEM_REQ_MSG_OPAQUE_FIELD(o,a,d)];
  assign addr   = msg[`VC_MEM_REQ_MSG_ADDR_FIELD(o,a,d)];
  assign len    = msg[`VC_MEM_REQ_MSG_LEN_FIELD(o,a,d)];
  assign data   = msg[`VC_MEM_REQ_MSG_DATA_FIELD(o,a,d)];

endmodule


//========================================================================
// Memory Response Message
//========================================================================
// Memory request messages can either be for a read or write. Read
// responses include an opaque field, the actual data, and the number of
// bytes, while write responses currently include just the opaque field.
//
// Message Format:
//
//    4b    p_opaque_nbits  calc   p_data_nbits
//  +------+---------------+------+------------------+
//  | type | opaque        | len  | data             |
//  +------+---------------+------+------------------+
//
// The message type is parameterized by the number of bits in the opaque
// field and data field. Note that the size of the length field is
// caclulated from the number of bits in the data field, and that the
// length field is expressed in _bytes_. If the value of the length field
// is zero, then the read or write should be for the full width of the
// data field.
//
// For example, if the opaque field is 8 bits and the data is 32 bits,
// then the message format is as follows:
//
//   45  42 41           34 33  32 31               0
//  +------+---------------+------+------------------+
//  | type | opaque        | len  | data             |
//  +------+---------------+------+------------------+
//
// The length field is two bits. A length value of one means one byte was
// read, a length value of two means two bytes were read, and so on. A
// length value of zero means all four bytes were read. Note that not all
// memories will necessarily support any alignment and/or any value for
// the length field.
//
// The opaque field is reserved for use by a specific implementation. All
// memories should guarantee that every response includes the opaque
// field corresponding to the request that generated the response.

//------------------------------------------------------------------------
// Memory Response Message: Message fields ordered from right to left
//------------------------------------------------------------------------
// We use the following short names to make all of these preprocessor
// macros more succinct.

// Data field

`define VC_MEM_RESP_MSG_DATA_NBITS(o_,d_)                               \
  d_

`define VC_MEM_RESP_MSG_DATA_MSB(o_,d_)                                 \
  ( `VC_MEM_RESP_MSG_DATA_NBITS(o_,d_) - 1 )

`define VC_MEM_RESP_MSG_DATA_FIELD(o_,d_)                               \
  (`VC_MEM_RESP_MSG_DATA_MSB(o_,d_)):                                   \
  0

// Length field

`define VC_MEM_RESP_MSG_LEN_NBITS(o_,d_)                                \
  ($clog2(d_/8))

`define VC_MEM_RESP_MSG_LEN_MSB(o_,d_)                                  \
  (   `VC_MEM_RESP_MSG_DATA_MSB(o_,d_)                                  \
    + `VC_MEM_RESP_MSG_LEN_NBITS(o_,d_) )

`define VC_MEM_RESP_MSG_LEN_FIELD(o_,d_)                                \
  (`VC_MEM_RESP_MSG_LEN_MSB(o_,d_)):                                    \
  (`VC_MEM_RESP_MSG_DATA_MSB(o_,d_) + 1)

// Opaque field

`define VC_MEM_RESP_MSG_OPAQUE_NBITS(o_,d_)                             \
  o_

`define VC_MEM_RESP_MSG_OPAQUE_MSB(o_,d_)                               \
  (   `VC_MEM_RESP_MSG_LEN_MSB(o_,d_)                                   \
    + `VC_MEM_RESP_MSG_OPAQUE_NBITS(o_,d_) )

`define VC_MEM_RESP_MSG_OPAQUE_FIELD(o_,d_)                             \
  (`VC_MEM_RESP_MSG_OPAQUE_MSB(o_,d_)):                                 \
  (`VC_MEM_RESP_MSG_LEN_MSB(o_,d_) + 1)

// Type field

`define VC_MEM_RESP_MSG_TYPE_NBITS(o_,d_) 3
`define VC_MEM_RESP_MSG_TYPE_READ     3'd0
`define VC_MEM_RESP_MSG_TYPE_WRITE    3'd1

// write no-refill
`define VC_MEM_RESP_MSG_TYPE_WRITE_INIT 2'd2
`define VC_MEM_RESP_MSG_TYPE_AMO_ADD    3'd3
`define VC_MEM_RESP_MSG_TYPE_AMO_AND    3'd4
`define VC_MEM_RESP_MSG_TYPE_AMO_OR     3'd5
`define VC_MEM_RESP_MSG_TYPE_X          3'dx

`define VC_MEM_RESP_MSG_TYPE_MSB(o_,d_)                                 \
  (   `VC_MEM_RESP_MSG_OPAQUE_MSB(o_,d_)                                \
    + `VC_MEM_RESP_MSG_TYPE_NBITS(o_,d_) )

`define VC_MEM_RESP_MSG_TYPE_FIELD(o_,d_)                               \
  (`VC_MEM_RESP_MSG_TYPE_MSB(o_,d_)):                                   \
  (`VC_MEM_RESP_MSG_OPAQUE_MSB(o_,d_) + 1)

// Total size of message

`define VC_MEM_RESP_MSG_NBITS(o_,d_)                                    \
  (   `VC_MEM_RESP_MSG_TYPE_NBITS(o_,d_)                                \
    + `VC_MEM_RESP_MSG_OPAQUE_NBITS(o_,d_)                              \
    + `VC_MEM_RESP_MSG_LEN_NBITS(o_,d_)                                 \
    + `VC_MEM_RESP_MSG_DATA_NBITS(o_,d_) )

//------------------------------------------------------------------------
// Memory Response Message: Pack message
//------------------------------------------------------------------------

module vc_MemRespMsgPack
#(
  parameter p_opaque_nbits = 8,
  parameter p_data_nbits   = 32,

  // Shorter names for message type, not to be set from outside the module
  parameter o = p_opaque_nbits,
  parameter d = p_data_nbits
)(
  // Input message

  input  [`VC_MEM_RESP_MSG_TYPE_NBITS(o,d)-1:0]   type,
  input  [`VC_MEM_RESP_MSG_OPAQUE_NBITS(o,d)-1:0] opaque,
  input  [`VC_MEM_RESP_MSG_LEN_NBITS(o,d)-1:0]    len,
  input  [`VC_MEM_RESP_MSG_DATA_NBITS(o,d)-1:0]   data,

  // Output bits

  output [`VC_MEM_RESP_MSG_NBITS(o,d)-1:0]        msg
);

  assign msg[`VC_MEM_RESP_MSG_TYPE_FIELD(o,d)]   = type;
  assign msg[`VC_MEM_RESP_MSG_OPAQUE_FIELD(o,d)] = opaque;
  assign msg[`VC_MEM_RESP_MSG_LEN_FIELD(o,d)]    = len;
  assign msg[`VC_MEM_RESP_MSG_DATA_FIELD(o,d)]   = data;

endmodule

//------------------------------------------------------------------------
// Memory Response Message: Unpack message
//------------------------------------------------------------------------

module vc_MemRespMsgUnpack
#(
  parameter p_opaque_nbits = 8,
  parameter p_data_nbits   = 32,

  // Shorter names for message type, not to be set from outside the module
  parameter o = p_opaque_nbits,
  parameter d = p_data_nbits
)(

  // Input bits

  input [`VC_MEM_RESP_MSG_NBITS(o,d)-1:0]         msg,

  // Output message

  output [`VC_MEM_RESP_MSG_TYPE_NBITS(o,d)-1:0]   type,
  output [`VC_MEM_RESP_MSG_OPAQUE_NBITS(o,d)-1:0] opaque,
  output [`VC_MEM_RESP_MSG_LEN_NBITS(o,d)-1:0]    len,
  output [`VC_MEM_RESP_MSG_DATA_NBITS(o,d)-1:0]   data
);

  assign type   = msg[`VC_MEM_RESP_MSG_TYPE_FIELD(o,d)];
  assign opaque = msg[`VC_MEM_RESP_MSG_OPAQUE_FIELD(o,d)];
  assign len    = msg[`VC_MEM_RESP_MSG_LEN_FIELD(o,d)];
  assign data   = msg[`VC_MEM_RESP_MSG_DATA_FIELD(o,d)];

endmodule

`endif /* VC_MEM_MSGS_V */

