module labelprop(
		 input {L} clk,
		 input seq {L} l_valid,
		 input [3:0] seq {L} l_status
		 );


   reg                 seq {L} final_data;
   reg                 seq {L} old_lbl;
   wire 	       seq {L} isMisspec;
   reg                 seq {L} tmp_data_tag;
   reg 		       seq {SPEC isMisspec, old_lbl} tmp_data;   
   reg                 seq {LH old_lbl} down;
   
   //begin all should succeed
   always@(*) begin     
      isMisspec = (l_valid && (l_status == tmp_data_tag)) ? 1 : 0;      
   end
   always@(posedge clk) begin
      old_lbl <= old_lbl;      
   end
   
   always@(posedge clk) begin
      if (isMisspec) begin
	 tmp_data <= 0;
	 tmp_data_tag <= 0;
	 down <= down;	 
      end else begin
	 tmp_data <= tmp_data;	 
	 tmp_data_tag <= tmp_data_tag;
	 down <= tmp_data; //this isn't what we want, but it makes sense w/ the type system	  
      end
   end

   always@(posedge clk) begin
      if (!isMisspec && old_lbl == 0)
	final_data <= tmp_data;
      else
	final_data <= final_data;
   end   
   //end all should succeed

   always@(posedge clk) begin
      tmp_data <= tmp_data; //fails since isMisspec might be true
      final_data <= (old_lbl == 0) ? tmp_data : final_data;      
   end
   
endmodule // labelprop

   
