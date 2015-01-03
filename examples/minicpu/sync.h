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
//  $Id: sync.h,v 1.2 1999/10/13 06:06:46 heinrich Exp $
//
//-------------------------------------------------------------------------

`include "finish.h"

task sync_setup;
   reg [31:0] i;
   begin
      // hostname portname #insns-to-skip sync-rate
      $sync_setup("localhost", 4000, 100, 1);
      for (i=0; i < 32; i=i+1) begin
	 CPU.regfile.RAM[i] = 0;
      end
   end
endtask

task sync_update;
   reg[31:0] i;
   begin
//      $display("%d, PC4 = %h, num_inst = %h\n",$time, CPU.PC4, CPU.num_instructions);
      if (CPU.num_instructions > 3) begin
         for (i=0; i<32; i=i+1) begin
	    $builtin_setregvalue (i, CPU.regfile.RAM[i]);
         end
         $builtin_setpc (CPU.PC4);
         if ($sync_send != 0) begin
   	    $sync_end;
  	    sim_finish;
	    for (i=0;i<32;i=i+1) begin
	       CPU.regfile.RAM[i] = $builtin_regvalue(i);
  	    end // for (i=0;i<32;i=i+1)
//   	    CPU.PC = $builtin_getpc;
         end
      end
   end
endtask // sync_update
