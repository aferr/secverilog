//////////////////////////////////////////////////////////////////////
////                                                              ////
////  A single-port combinational RAM module                      ////
////                                                              ////
//////////////////////////////////////////////////////////////////////

`ifdef NOSYNTH

`include "cache.h"

module idram_dw (
	clk, index, offset, din, dout, we, en
);

parameter set = 0;
parameter dw = 32;
parameter aw = (`I_INDEX_WIDTH+`I_WO_WIDTH);	// log2(num of entries)
parameter num = (1 << aw);			// num of entries
parameter init_file = "";

input				clk;
input	[`I_INDEX_WIDTH-1:0]	index;
input	[`I_WO_WIDTH-1:0]	offset;
input	[dw-1:0]		din;
output	[dw*2-1:0]		dout;
input				we;
input				en;

reg 	[dw-1:0] 		mem [0:num-1];
reg	[dw*2-1:0]		dout;

integer	i;

initial begin
    for (i = 0; i < num; i = i+1) mem[i] = {dw{1'b0}};

    if (init_file != "") begin
        $readmemh(init_file, mem, 0, num-1);
    end
end

always @(posedge clk) begin
	if (we & en) begin
		mem[{index,offset}] = din;
	end
end

always @(*) begin
  if (en) dout = { mem[{index,offset[`I_WO_WIDTH-1:1],1'b1}], mem[{index,offset[`I_WO_WIDTH-1:1],1'b0}] };

end

endmodule
`endif //  `ifdef NOSYNTH

`ifndef NOSYNTH

module idram_dw (
	clk, index, offset, din, dout, we, en
)
  /* synthesis syn_black_box
  syn_tpd1 = "index[`I_WO_WIDTH-1:0]->dout[dw-1:0]=10.0" */;

parameter set = 0;
parameter dw = 32;
parameter aw = (`I_INDEX_WIDTH+`I_WO_WIDTH);	// log2(num of entries)
parameter num = (1 << aw);			// num of entries
parameter init_file = "";

input				clk;
input	[`I_INDEX_WIDTH-1:0]	index;
input	[`I_WO_WIDTH-1:0]	offset;
input	[dw-1:0]	din;
output	[dw*2-1:0]	dout;
input			we;
input			en;

endmodule   
`endif
