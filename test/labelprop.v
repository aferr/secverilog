module labelprop(
		 input {L} clk,
		 input {L} rst,
		 input seq {L} l_in,
		 input seq {Domain l_in} d_in
		 );

   reg seq {L} n_lbl;
   reg seq {Domain n_lbl} n_data;

   reg seq {L} n_lbl_2;
   reg seq {Domain n_lbl_2} n_data_2;

   
   always@(posedge clk) begin
      if (rst) begin	
	 n_lbl <= 0;
	 n_data <= 0;	 
      end else begin
	 n_lbl <= l_in;
	 n_data <= d_in;	 
      end	 
   end

   always@(posedge clk) begin
      n_lbl_2 <= n_lbl;
      n_data_2 <= n_data;
   end

      
endmodule // labelprop

   
