
module array(clk, reset, sel);

   input {L} clk;
   input {L} reset;
   input {L} sel;
   
   wire [15:0] {H} sec_data_val;
   wire [3:0]  {H} sec_index_val;

   wire [15:0] {L} pub_data_val;
   wire [3:0]  {L} pub_index_val;
   
   reg [15:0] seq {L} data_array[3:0];
   reg [15:0] {L} data_array_com[3:0];


   always@(posedge clk) begin
      if (sel) begin
	 data_array[pub_index_val] <= pub_data_val; //success
         data_array[sec_index_val] <= pub_data_val; //fail
	 data_array[0][3:0] <= pub_index_val; //success
	 data_array[0][sec_index_val] <= pub_index_val; //fail	 
      end else begin
	 data_array[pub_index_val] <= sec_data_val; //fail
	 data_array[sec_index_val] <= sec_data_val; //fail
	 data_array[0][3:0] <= sec_index_val; //fail
	 data_array[0][sec_index_val] <= sec_index_val; //fail	 	 
      end
   end


   always@(*) begin
      if (sel) begin
	 data_array_com[pub_index_val] = pub_data_val; //success
         data_array_com[sec_index_val] = pub_data_val; //fail
	 data_array_com[0][3:0] = pub_index_val; //success
	 data_array_com[0][sec_index_val] = pub_index_val; //fail	 
      end else begin
	 data_array_com[pub_index_val] = sec_data_val; //fail
	 data_array_com[sec_index_val] = sec_data_val; //fail
	 data_array_com[0][3:0] = sec_index_val; //fail
	 data_array_com[0][sec_index_val] = sec_index_val; //fail	 	 
      end
   end
   
  

   
endmodule // array
