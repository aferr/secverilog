module behave(clk, reset, secret);

   input {L} clk;
   input {L} reset;
   input {H} secret;
   
   reg seq {L} in[3:0];   

   reg [3:0] com {Par x} x = 0;
   reg [3:0] com {Par y} y = 0;      
   reg [3:0] seq {L} data;
   reg [3:0] seq {Par d2} d2;   
   genvar    i;   

   generate
      for (i = 0; i <= 3; i = i +1) begin
	 always@(*) begin
	    if (in[i] == 1) begin
	       x = x + 1; //succeed, only upgrade
	       y = y - 1; //fail, potential downgrade	       
	    end
	 end	 
      end
   endgenerate   

   always@(posedge clk) begin
      if (reset) begin
	 data <= x; //fail
	 d2 <= x; //succeed	 
      end else begin
	 data <= y; //fail
	 d2 <= y; //succeed
      end
   end

   always@(*) begin
      if (x == 1) begin
	 x = 0; //should fail
	 y = 1; //should fail nsu check	 
      end
   end
      
endmodule
