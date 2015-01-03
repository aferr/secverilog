//////////////////////////////////////////////////////////////////////
////                                                              ////
////  A single-port combinational RAM module                      ////
////                                                              ////
//////////////////////////////////////////////////////////////////////

`include "cache.h"

`ifdef NOSYNTH

module idram (
	clk, index, way, offset, din, dout0, dout1, dout2, dout3, we, en
);

parameter set = 0;
parameter dw = 32;
parameter aw = (`I_INDEX_WIDTH+`I_WO_WIDTH);	// log2(num of entries)
parameter num = (1 << aw);			// num of entries
parameter init_file = "";

input				clk;
input	[`I_INDEX_WIDTH-1:0] index;
input	[1:0]			 way;
input	[`I_WO_WIDTH-1:0]	 offset;
input	[dw-1:0]		din;
output	[dw-1:0]		dout0;
output	[dw-1:0]		dout1;
output	[dw-1:0]		dout2;
output	[dw-1:0]		dout3;
input				we;
input				en;

reg 	[dw-1:0] 		 mem0[0:num-1];
reg 	[dw-1:0] 		 mem1[0:num-1];
reg 	[dw-1:0] 		 mem2[0:num-1];
reg 	[dw-1:0] 		 mem3[0:num-1];

reg	[dw-1:0]		 dout0;
reg	[dw-1:0]		 dout1;
reg	[dw-1:0]		 dout2;
reg	[dw-1:0]		 dout3;

integer	i;

initial begin
    for (i = 0; i < num; i = i+1) begin
		mem0[i] = {dw{1'b0}};
		mem1[i] = {dw{1'b0}};
		mem2[i] = {dw{1'b0}};
		mem3[i] = {dw{1'b0}};  
	end

    if (init_file != "") begin
        $readmemh(init_file, mem0, 0, num-1);
        $readmemh(init_file, mem1, 0, num-1);
        $readmemh(init_file, mem2, 0, num-1);
        $readmemh(init_file, mem3, 0, num-1);
    end
end

always @(posedge clk) begin
	if (we & en) begin
        case (way)
            2'b00: begin
                mem0[{index,offset}] = din;
            end
            2'b01: begin
                mem1[{index,offset}] = din;
            end
            2'b10: begin
                mem2[{index,offset}] = din;
            end
            2'b11: begin
                mem3[{index,offset}] = din;
            end
        endcase
	end
end

always @(*) begin
	if (en) begin
		dout0 = mem0[{index,offset}];
		dout1 = mem1[{index,offset}];
		dout2 = mem2[{index,offset}];
		dout3 = mem3[{index,offset}];
	end
end

endmodule
`endif //  `ifdef NOSYNTH

`ifndef NOSYNTH

module idram (
	clk, index, offset, din, dout, we, en
)
  /* synthesis syn_black_box
  syn_tpd1 = "index[`D_INDEX_WIDTH-1:0]->dout[dw-1:0]=10.0" */;

parameter set = 0;
parameter dw = 32;
parameter aw = (`I_INDEX_WIDTH+`I_WO_WIDTH);	// log2(num of entries)
parameter num = (1 << aw);			// num of entries
parameter init_file = "";

input				clk;
input	[`I_INDEX_WIDTH-1:0]	index;
input	[`I_WO_WIDTH-1:0]	offset;
input	[dw-1:0]	din;
output	[dw-1:0]	dout;
input			we;
input			en;

endmodule   
`endif

