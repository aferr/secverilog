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
//  $Id: finish.h,v 1.1 2000/01/18 15:51:43 rajit Exp $
//
//-------------------------------------------------------------------------

//
//  Simulations cleanup routine
//
`ifdef NOSYNTH
task sim_finish;
    begin
       $display("Number of loads = %d", CPU.numLoads);
       $display("Number of stores = %d", CPU.numStores);
       $display("Number of D$ hits = %d", (CPU.numStores+CPU.numLoads) - CPU.numDMisses);
       $display("Number of D$ references = %d", CPU.numStores+CPU.numLoads);
       $display("Number of I$ hits = %d", CPU.num_instructions-CPU.numIMisses);
       $display("Number of I$ references = %d\n", CPU.num_instructions);
    end
endtask
`endif