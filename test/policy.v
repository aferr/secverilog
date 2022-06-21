module policy(
	      input clk,
	      input rst,
	      input invalid
);


   reg 		    seq {erase(L;epol invalid;();H)} data_reg;


   always@(posedge clk) begin
      if (rst) data_reg <= 0;
      else data_reg <= data_reg; //should fail because policy may be true this cycle and become false next cycle
   end
      
endmodule
