`include "deptype-example.v"

module testmodule(
  input {L} clk,
  output reg [15:0] {L} out		 
  );   

   wire [15:0] 	    {H} data1 = 0;     
   wire [15:0] 	    {H} data2 = 100;
   reg [15:0] 	    {L} timer;
 
   wire [15:0] 	    {L} out1;
   wire [15:0] 	    {L} out2;
 
  deptype test1
    (
     .clk (clk),
     .timer (timer),
     .data (data1), //should violate an assumption
     .out (out1)
     );

  deptype test2
    (
     .clk (clk),
     .timer (timer),
     .data (data2), //does not violate the assumption
     .out (out2)
     );

   always@(posedge clk)
     begin
	timer <= timer + 1;	
     end

   always@(posedge clk)
     begin
	out <= (timer[0] == 0) ? out1 : out2;
     end
endmodule
