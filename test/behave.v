module behave(clk, reset, secret);

   input {L} clk;
   input {L} reset;
   input {H} secret;
   
   reg seq {L} in[3:0];   

   reg [3:0] com {Par x} x = 0;
   reg [3:0] com {Par y} y = 0;
   reg [3:0] com {Par z} z = 0;
   reg [3:0] com {Par a} a = 0;
   reg [3:0] com {Par b} b = 0;   
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

   reg [4:0] com {L} j;
   
   always@(*) begin
      for(j = 0; j < 3; j = j + 1) begin
	 if (!reset) begin
	    b = j;
	 end
      end
   end
   
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

   always@(*) begin
      z = 0; //succeed
      if (secret) begin
	 z = 2; //should fail nsu check
      end
   end

   always@(*) begin
      a = 0;      
      case (secret)
	0: begin
	   a = 1;//should fail nsu check	   
	end
	1: begin
	   a = 1;//should fail nsu check
	end
      endcase
   end // always@ (*)

endmodule
