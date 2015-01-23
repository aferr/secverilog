module arrtype();

//wire { |i| H } foo [0:7];
wire { L } foo [0:7];
wire [0:7] {|i| Par 0} bar;
integer j = 2;

assign bar[7] = foo[2];
assign foo[7] = bar[2];

endmodule
