module arrtype();

wire { |i| a | b} foo [0:7];
wire [0:7] {L} bar;

assign bar[7] = foo[7];

endmodule
