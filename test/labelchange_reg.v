module labelchange_reg(
    input  clk,
    input  rst,
    input  data_in,
    input  w_en2,
    input  lbl_in_2,
    input  data_in_2, 
    output data_out
);
   
   wire    com {L} data_in;
   wire    seq {H} data_out;
   
   wire    com {L} w_en2;
   wire    com {L} lbl_in_2;
   wire    com {LH lbl_in_2}  data_in_2;
   
   reg 	   seq {L} pub_data;
   reg 	   seq {L} lbl_reg;
   reg 	   seq {LH lbl_reg} lbl_data;
   
   
   always@(posedge clk) begin
      if(rst) data_out <= data_in;
      else data_out <= data_in;
   end

   always@(posedge clk) begin
      if (rst || w_en2) begin
	 pub_data <= (rst) ? 0 : 
		     (!lbl_in_2) ? data_in_2 : 0;
	 lbl_reg <= (rst) ? 0 : lbl_in_2;
	 lbl_data <= (rst) ? 0 : data_in_2;	 
      end
   end
endmodule
