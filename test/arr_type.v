module arrtype();

//wire { |i| H } foo [0:7];
wire { L } foo [0:7];
wire [0:7] {|i| Par i} bar;
wire [0:7] {|i| Par 0} baz;
wire [2:0] j;

assign j = 3'd2;

assign bar[0] = foo[3];
assign foo[0] = bar[j];
assign foo[7] = baz[1];

endmodule
