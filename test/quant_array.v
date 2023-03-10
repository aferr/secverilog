module quant_array();

   input {L} clk;

   input [3:0] {L} idx;
   input [3:0] {L} idx2;
   input [2:0] {L} low_data;
   input [2:0] {H} high_data;

   input       {L} cond1;
   input       {L} cond2;

   reg seq {L} tags[15:0];

   reg [2:0] seq {|i| LH_ARRAY tags,i} data[15:0];

   reg [2:0] seq {|j| LH_ARRAY tags,j} data2[15:0];

   reg 	seq {|k| LH_ARRAY recData, k} recData[15:0];


   genvar    datai;
   generate
      for (datai = 0; datai <= 15; datai = datai + 1)
	begin
	   always @(posedge clk) begin
	      // tags[datai] <= tags[datai];
	      data[datai] <= data[datai];
	      if (high_data == 0) begin
		 recData[datai] <= 1;
	      end
	   end
	end
   endgenerate

   always @(posedge clk)
     begin
	if (tags[idx] == 0)
	  data2[idx] <= low_data;
	else
	  data2[idx] <= high_data;
     end

   always @(posedge clk)
     begin
	data2[idx2] <= high_data;
     end

endmodule
