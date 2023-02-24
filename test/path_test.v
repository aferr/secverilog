module path_test(clk);

   input {L} clk;

   reg [2:0] seq {Domain w} w;
   reg [2:0] seq {Domain x} x;
   reg [2:0] seq {Domain w} y;

   reg {L} a;
   reg {L} b;
   reg {L} c;
   reg {L} d;

   reg [2:0] {Domain non_seq} non_seq;
   

   always @(posedge clk) begin
      w <= 3;
      if (a) begin
         if (!b) begin
            if (c && d) begin
               x <= 1;
            end
            y <= 1;
         end
      end
   end // always @ (posedge clk)

   always @(*) begin
      if (a) begin
         if (!b) begin
            non_seq = 2;
         end
      end
   end
   




endmodule
