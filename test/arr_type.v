module arrtype();

//wire { |i| H } foo [0:7];
wire { L } foo [0:7];
wire [0:7] {|i| H} bar;
integer j = 2;

assign bar[7] = foo[7];

assign bar[0] = foo[j];

endmodule
