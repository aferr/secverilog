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
      n_lbl <= l_in;
      n_data <= d_in;
      n_lbl_2 <= n_lbl;
      n_data_2 <= n_data;      
   end


// //translation:
//    always@(posedge clk) begin
//       n_lbl_next <= l_in;
//       n_data_next <= d_in;
//       n_lbl_2_next <= n_lbl;
//       n_data_2_next <= n_data;            
//       n_data = n_data_next;
//       n_data_2 = n_data_2_next;
//       n_lbl = n_lbl_next;
//       n_lbl_2 = n_lbl_2_next;      
//    end
// //end translation

//    //translation we want:
//    always@(posedge clk) begin
//       n_lbl <= n_lbl_next;
//       n_data <= n_data_next;
//       n_lbl_2 <= n_lbl_2_next;
//       n_data_2 <= n_data_2_next;
//    end
//    always@(*) begin
//       n_lbl_next = l_in;
//       n_data_next = d_in;
//       n_lbl_2_next = n_lbl;
//       n_dat_2_next = n_data;      
//    end
      
endmodule // labelprop

   
