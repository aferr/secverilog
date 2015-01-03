//-*-mode:verilog-*-------------------------------------------------------
//
//  Copyright (c) 1999 Cornell University
//  Computer Systems Laboratory
//  Cornell University, Ithaca, NY 14853
//  All Rights Reserved
//
//  Permission to use, copy, modify, and distribute this software
//  and its documentation for any purpose and without fee is hereby
//  granted, provided that the above copyright notice appear in all
//  copies. Cornell University makes no representations
//  about the suitability of this software for any purpose. It is
//  provided "as is" without express or implied warranty. Export of this
//  software outside of the United States of America may require an
//  export license.
//
//  $Id: sysfunc.h,v 1.1 1999/10/13 04:46:43 heinrich Exp $
//
//-------------------------------------------------------------------------

//
//  Interface to system calls
//

`ifdef NOSYNTH
`include "finish.h"

task syscall;
   
   reg[31:0] i;
   reg[31:0] op_code;
   reg[31:0] length;
   reg[31:0] addr;
   reg[`D_INDEX_WIDTH-1:0] addrIndex;
     
   begin
      // get system call id, and the address for a read
      addr = CPU.regfile.RAM[5];
      op_code = CPU.regfile.RAM[2];

      // store register file state to the C interface functions!
      for (i=1; i<32;i=i+1)
	begin
	   // Changed to setreg instead of setregvalue 
	   $syscall_setreg (i,CPU.regfile.RAM[i]);
	 end
      $syscall_setpc (CPU.PC);	// store PC

      // do the system call
      if ($emulate_syscall) begin
	 // exit called
	 $display ("-----------------------------------");
	 $display ("Program Terminated.");
	 $display ("Executed %d instructions", CPU.num_instructions);
	 $display ("Ran for %d cycles",$time/`cycle);	 
	 $display ("-----------------------------------");
	 sim_finish;
	 $finish;	 
      end

      // restore register file state from the C interface
      //$display("Restoring regfile from C interface\n");      
      for (i=1; i<32;i=i+1)
	begin
	   // Changed to syscall_getreg instead of syscall_regvalue
	    CPU.regfile.RAM[i] = $syscall_getreg(i);
	 end

      // for the read syscall, we need to invalidate the data cache in the
      // processor, since it's already updated in the main mem the trouble is
      // that it triggers a lot of cache misses. Seems a better way is to
      // update the content directly (the commentted lines), but it does not
      // work somehow
      if (op_code == 4003) begin 
         //$display ("calling read");
         length = CPU.regfile.RAM[2];
         //$display ("length is %d, addr is %x", length, addr);

	 // now, mark all touched memory in the read as invalid. There is no
	 // need to write them black since the value in memory (updated by the
	 // simulator) is more recent calculate index of addr 
         for (i=addr; i < addr + length; i = i+4) begin
             addrIndex = i[`D_INDEX];
             //$display ("addr is %x, %x", i, $load_mm({i[31:2], 2'b0}));
             if ((CPU.MEMcontr.dc_tmem.mem0[addrIndex] == i[`D_TAG]) 
               & (CPU.MEMcontr.dc_tmem.mem0[addrIndex][`D_VALID])) begin
                 CPU.MEMcontr.dc_tmem.mem0[addrIndex][`D_VALID] = 1'b0;
                 //CPU.MEMcontr.dc_dmem.mem0[addrIndex] = $load_mm({i[31:2], 2'b0});
                 //CPU.MEMcontr.dc_smem.mem0[addrIndex][`D_DIRTY] = 1'b1;
             end
             if ((CPU.MEMcontr.dc_tmem.mem1[addrIndex] == i[`D_TAG]) 
               & (CPU.MEMcontr.dc_tmem.mem1[addrIndex][`D_VALID])) begin
                 CPU.MEMcontr.dc_tmem.mem1[addrIndex][`D_VALID] = 1'b0;
                 //CPU.MEMcontr.dc_dmem.mem1[addrIndex] = $load_mm({i[31:2], 2'b0});
                 //CPU.MEMcontr.dc_smem.mem1[addrIndex][`D_DIRTY] = 1'b1;
             end
             if ((CPU.MEMcontr.dc_tmem.mem2[addrIndex] == i[`D_TAG]) 
               & (CPU.MEMcontr.dc_tmem.mem2[addrIndex][`D_VALID])) begin
                 CPU.MEMcontr.dc_tmem.mem2[addrIndex][`D_VALID] = 1'b0;
                 //CPU.MEMcontr.dc_dmem.mem2[addrIndex] = $load_mm({i[31:2], 2'b0});
                 //CPU.MEMcontr.dc_smem.mem2[addrIndex][`D_DIRTY] = 1'b1;
             end
             if ((CPU.MEMcontr.dc_tmem.mem3[addrIndex] == i[`D_TAG]) 
               & (CPU.MEMcontr.dc_tmem.mem3[addrIndex][`D_VALID])) begin
                 CPU.MEMcontr.dc_tmem.mem3[addrIndex][`D_VALID] = 1'b0;
                 //CPU.MEMcontr.dc_dmem.mem3[addrIndex] = $load_mm({i[31:2], 2'b0});
                 //CPU.MEMcontr.dc_smem.mem3[addrIndex][`D_DIRTY] = 1'b1;
             end
         end
      end 
   end
endtask

	 
			  

`endif
