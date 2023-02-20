module nsu(
	   input {H} h1,
	   input {L} clk
	   );

   reg seq {LH x} x;
   reg seq {L} l1;
   reg seq {L} l2;   
   
   always@(posedge clk) begin
      if (h1) begin
	 x <= 1;
      end
      if (x == 0 && l1 == 1) begin
	 l1 <= 0;	 
      end
      l2 <= 1;      
   end
   
endmodule
