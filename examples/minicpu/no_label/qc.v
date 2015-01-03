//-------------------------------------------------------------------------
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
//  $Id: qc.v,v 1.2 1999/10/18 17:58:51 heinrich Exp $
//
//-------------------------------------------------------------------------

/* The quick compare logic computes results for 6 different types 
 * conditions for use with conditional branches.  QCsel specifies 
 * the type of comparision to be computed. */ 

`include "mips.h"

module qc (RSbus, RTbus, QCsel, Result, ReadLabel, WriteLabel);

input	[31:0]	RSbus;		// S operand input
input	[31:0]	RTbus;		// T operand input
input	[5:0]	QCsel;		// Select comparision operation
input		 ReadLabel;
input		 WriteLabel;
output	Result;	
reg	Result;			// Result of comparision operation

// The compare logic happens in the EX stage in the MIPS pipeline.  The
// RSbus and RTbus inputs passed in when this module is instantiated 
// (in cpu.v) should be the outputs of the bypass muxes so that we are
// comparing the proper registers

always @(RSbus or RTbus or QCsel) begin
   case (QCsel)
      `select_qc_ne:	Result = (RSbus != RTbus);  // BNE
      `select_qc_eq:	Result = (RSbus == RTbus);  // BEQ
      `select_qc_lez:	Result = (RSbus[31] == 1) | (RSbus == 0); // BLEZ
      `select_qc_gtz:	Result = (RSbus[31] == 0) & (RSbus != 0); // BGTZ
      `select_qc_gez:	Result = (RSbus[31] == 0);  // BGEZ
      `select_qc_ltz:	Result = (RSbus[31] == 1);  // BLTZ
      default:		Result = `dc;	            // Undefined
   endcase
end

endmodule		

