/* 
 * This example tests a lattice with four labels: L, H, D1, D2.
 */
module diamond();

reg[1:0] {L} low;
reg[1:0] {H} high;
reg[1:0] {D1} d1;
reg[1:0] {D2} d2;


// domains with dependent types
// notice there are only two domains, so x, y are 1-bit long
reg {Domain x} x;
reg {Domain y} y;

// this should work, since when x is 0, label of x is Domain 0 == D1
always @(*) begin
	if (x == 0) begin
		d1 = x;
	end
end

// this should work
always @(*) begin
	if (x == 1) begin
		d2 = x;
	end
end

// this should fail
always @(*) begin
	d2 = d1;
end

// this should fail
always @(*) begin
	d1 = d2;
end


endmodule
