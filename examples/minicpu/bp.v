`include "mips.h"
   
module bpcontr (addr, MemRDaddr, RDaddr, BPsel, ReadLabel, WriteLabel);

input	[4:0]	addr;	   // Source reg address specifier
input	[4:0]	MemRDaddr; // Dest reg in MEM
input	[4:0]	RDaddr;	   // Dest reg in WB
input		{L} ReadLabel;
input		{L} WriteLabel;

output	[1:0]	BPsel;	// Forwarding select	
reg     [1:0]	BPsel;

/*---------------------------------------------------------------------
Data Forwarding Select

The following logic examine the source reg address, stage 3 destination
reg address and stage 4 destination reg address in oder to make select
signal for the forwarding demux.
---------------------------------------------------------------------*/

always @(addr or MemRDaddr or RDaddr) begin
   if (addr == 5'b0) begin
      BPsel = `select_bp_reg;
   end
   else if (addr == MemRDaddr) begin
      BPsel = `select_bp_stage3;
      end
   else if (addr == RDaddr) begin
      BPsel = `select_bp_stage4;
   end
   else begin
      BPsel = `select_bp_reg;
   end
end

endmodule
