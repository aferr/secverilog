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
//  copies. Cornell University makes no representation
//  about the suitability of this software for any purpose. It is
//  provided "as is" without express or implied warranty. Export of this
//  software outside of the United States of America may require an
//  export license.
//  
//-------------------------------------------------------------------------

`include "mips.h"

module multdiv (
  input              iCLK,
  input              iReset,
  input      [31:0]  iRS,
  input      [31:0]  iRT,
  input      [2:0]   iMDtype,
  input              iHold,        // If asserted, multdiv pipeline does not change this cycle
  input              iKill,        // If asserted, multdiv pipeline is reset to first cycle
  output reg [31:0]  oLO,
  output reg [31:0]  oHI,
  output             oReady        // 1 when ready for new input (which is also when HI and LO are valid)
);
  
  reg        [5:0]   mdCntr;                   // which clock cycle of the mult/div is the processor on? (0-32)
  reg                done;                     // 1 when current mult/div is done or not currently working on mult/div
  reg        [2:0]   currentMDtype;            // current instruction type (MULT 100, MULTU 101, DIV 110, DIVU 111, others 000)
  reg                RSsign;                   // sign of RS (1 is negative, 0 is positive)
  reg                RTsign;                   // sign of RT (1 is negative, 0 is positive)
  reg        [31:0]  plierQuot;                // holds the multiplier in MULT/MULTU, and the quotient in DIV/DIVU
  reg        [63:0]  candDivisor;              // holds the multiplicand in MULT/MULTU, and the divisor in DIV/DIVU
  reg        [63:0]  prodRem;                  // holds the product in MULT/MULTU, and the remainder in DIV/DIVU
  
  wire       [63:0]  remMinusDiv;              // used during division as (remainder-divisor)
  wire       [63:0]  remMinusDivU;             // used only on the first clock cycle of DIVU, before the remainder and divisor registers have been written
  
  assign remMinusDiv  = prodRem - candDivisor;
  assign remMinusDivU = {32'b0, iRS} - {1'b0, iRT, 31'b0};
  assign oReady       = done | iKill;
  
  always @(posedge iCLK) begin
    if (iReset) begin
      mdCntr        <= 6'b0;
      done          <= 1'b1;
      currentMDtype <= `mdtype_none;
    end
    else if(~iHold) begin
      
      if ((mdCntr == 31) | iKill) begin
        // When mdCntr becomes 32 or the mult/div is killed without being replaced,
        // the calculating is done.
        done <= 1'b1;
      end
      else if (iMDtype != `mdtype_none) begin
        // If the next instruction will be a multiply/divide instruction,
        // go back to being not done.
        done <= 1'b0;
      end
      
      if (oReady) begin
        // What to do when first beginning a new instruction
        // (done previous mult/div or killed)
        mdCntr        <= 6'b0;
        currentMDtype <= iMDtype;
        
        // Buffer signs of operands
        RSsign       <= iRS[31];
        RTsign       <= iRT[31];
        
        // perform first step of mult/div instruction
        if(iMDtype == `mdtype_mult) begin           // for MULT, first step is to convert multiplier and multiplicand to positives
  		// $display("iRS: %h", iRS);
  		// $display("iRT: %h", iRT);
		  plierQuot   <= iRT[31] ? ~iRT+1 : iRT;
          candDivisor <= {32'b0, (iRS[31] ? ~iRS+1 : iRS)};
          prodRem     <= 64'b0;
        end
        else if(iMDtype == `mdtype_multu) begin     // for MULTU, first step is same as next 31, but using initial values
          plierQuot   <= {1'b0, iRT[31:1]};
          candDivisor <= {31'b0, iRS, 1'b0};
          prodRem     <= iRT[0] ? {32'b0, iRS} : 64'b0;
        end
        else if(iMDtype == `mdtype_div) begin       // for DIV, first step is to convert the divisor and dividend (first stored in remainder) to positives
          plierQuot   <= 32'b0;
          candDivisor <= {2'b0, (iRT[31] ? ~iRT+1 : iRT), 30'b0};
          prodRem     <= {32'b0, (iRS[31] ? ~iRS+1 : iRS)};
        end
        else if(iMDtype == `mdtype_divu) begin      // for DIVU, first step is same as next 31, but using initial values
          plierQuot   <= {31'b0, ~remMinusDivU[63]};
          candDivisor <= {2'b0, iRT, 30'b0};
          prodRem     <= remMinusDivU[63] ? {32'b0, iRS} : remMinusDivU;
        end
        
      end
      
      else begin
        // What to do when working on a mult/div instruction
        mdCntr       <= mdCntr+1;
        
        // MULT
		//$display("MULTDIV: %b %d", currentMDtype, mdCntr);
		// $display("iMDtype: %h", iMDtype);
		// $display("plierQuot: %h", plierQuot);
		// $display("candDivisor: %h", candDivisor);
		// $display("product: %h", prodRem);
        if (currentMDtype == `mdtype_mult) begin
          if (mdCntr == 31) begin // for MULT, negate product if the multiplier and multiplicand signs disagree
            {oHI, oLO}  <= RTsign==RSsign ? prodRem : ~prodRem+1;
          end
          else begin
            plierQuot   <= {1'b0, plierQuot[31:1]};                      // shift multiplier right one
            candDivisor <= {candDivisor[62:0], 1'b0};                    // shift multiplicand left one
            prodRem     <= plierQuot[0] ? prodRem+candDivisor : prodRem; // add multiplicand to product if multiplier[0] == 1
          end
        end
        
        // MULTU
        if (currentMDtype == `mdtype_multu) begin
          if (mdCntr == 31) begin // for MULTU, export product as simply what is in the product register
            {oHI, oLO}  <= prodRem;            // {HI,LO} <= product
          end
          else begin
            plierQuot   <= {1'b0, plierQuot[31:1]};                      // shift multiplier right one
            candDivisor <= {candDivisor[62:0], 1'b0};                    // shift multiplicand left one
            prodRem     <= plierQuot[0] ? prodRem+candDivisor : prodRem; // add multiplicand to product if multiplier[0] == 1
          end
        end
        
        // DIV
        if (currentMDtype == `mdtype_div) begin
          if (mdCntr == 31) begin // for DIV, signs of outputs depend on signs of inputs
            oHI         <= RSsign ? ~prodRem[31:0]+1 : prodRem;       // remainder is same sign as dividend
            oLO         <= RSsign==RTsign ? plierQuot : ~plierQuot+1; // quotient is negative if dividend and divisor signs disagree
          end
          else begin
            plierQuot   <= {plierQuot[30:0], ~remMinusDiv[63]};       // shift quotient left and pass in 1 if (remainder-divisor) is still positive
            candDivisor <= {1'b0, candDivisor[63:1]};                 // shift divisor right one
            prodRem     <= remMinusDiv[63] ? prodRem : remMinusDiv;   // subtract divisor from remainder if the result is still positive
          end
        end
        
        // DIVU
        if (currentMDtype == `mdtype_divu) begin
          if (mdCntr == 31) begin // for DIVU, export remainder as HI and quotient as LO
            oHI         <= prodRem[31:0];      // HI <= remainder
            oLO         <= plierQuot;          // LO <= quotient
          end
          else begin
            plierQuot   <= {plierQuot[30:0], ~remMinusDiv[63]};       // shift quotient left and pass in 1 if (remainder-divisor) is still positive
            candDivisor <= {1'b0, candDivisor[63:1]};                 // shift divisor right one
            prodRem     <= remMinusDiv[63] ? prodRem : remMinusDiv;   // subtract divisor from remainder if the result is still positive
          end
        end
        
      end
    end
  end
endmodule // multdiv
