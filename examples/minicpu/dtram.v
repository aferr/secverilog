//////////////////////////////////////////////////////////////////////
////                                                              ////
////  A single-port combinational RAM module                      ////
////                                                              ////
//////////////////////////////////////////////////////////////////////

`include "cache.h"

`ifdef NOSYNTH

module dtram (
	clk, index, way, din, dout0, dout1, dout2, dout3, we, en
);

parameter set = 0;
parameter dw = `D_TAG_WIDTH;
parameter aw = `D_INDEX_WIDTH;	// log2(num of cache sets)
parameter num = (1 << aw);			// num of cache sets
parameter init_file = "";

input				clk;
input	[`D_INDEX_WIDTH-1:0]	index;
input	[1:0]			{Way way} way;
input	[dw-1:0]		din;
output	[dw-1:0]		dout0;
output	[dw-1:0]		dout1;
output	[dw-1:0]		dout2;
output	[dw-1:0]		dout3;
input				we;
input				en;

reg 	[dw-1:0] 		{L} mem0 [0:num-1];
reg 	[dw-1:0] 		{L} mem1 [0:num-1];
reg 	[dw-1:0] 		{H} mem2 [0:num-1];
reg 	[dw-1:0] 		{H} mem3 [0:num-1];

reg	[dw-1:0]		{Par ReadLabel} dout0;
reg	[dw-1:0]		{Par ReadLabel} dout1;
reg	[dw-1:0]		{H} dout2;
reg	[dw-1:0]		{H} dout3;

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
                mem0[index] = din;
            end
            2'b01: begin
                mem1[index] = din;
            end
            2'b10: begin
                mem2[index] = din;
            end
            2'b11: begin
                mem3[index] = din;
            end
        endcase
		$dcache_tag_write(index,way,din);
	end
end

always @(*) begin
	if (en) begin
		dout0 = mem0[index];
		dout1 = mem1[index];
		dout2 = mem2[index];
		dout3 = mem3[index];
	end
	//else dout = {dw{1'b0}};
end

endmodule
`endif //  `ifdef NOSYNTH

`ifndef NOSYNTH

module dtram (
	clk, index, din, dout, we, en
)
  /* synthesis syn_black_box
  syn_tpd1 = "index[aw-1:0]->dout[dw-1:0]=10.0" */;

parameter set = 0;
parameter dw = `D_TAG_WIDTH;
parameter aw = `D_INDEX_WIDTH;	// log2(num of entries)
parameter num = (1 << aw);			// num of entries
parameter init_file = "";

input				clk;
input	[`D_INDEX_WIDTH-1:0]	index;
input	[dw-1:0]		din;
output	[dw-1:0]		dout;
input				we;
input				en;

endmodule   
`endif

