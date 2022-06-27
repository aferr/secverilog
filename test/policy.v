module policy(
	      input clk,
	      input rst,
	      input invalid,
	      output {H} out
);


   reg 		    seq {erase(L;epol invalid;();H)} data_reg;
   reg 		    seq {erase(L;epol invalid;();H)} dreg_2;   


   always@(posedge clk) begin
      if (rst) data_reg <= 0;
      else data_reg <= data_reg; //should fail because policy may be true this cycle and become false next cycle
   end

   always@(posedge clk) begin
      if (rst || invalid) dreg_2 <= 0;
      else dreg_2 <= dreg_2; //should succeed because we don't copy if data was invalid
   end

   assign out = (invalid) ? data_reg : 0;
   
endmodule
