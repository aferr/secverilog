module test_literal(input {L} clk);

  reg seq {LH 1} high_data;
   reg seq {LH 0} low_data;

   always@(posedge clk) begin
      high_data <= low_data;
   end


endmodule
