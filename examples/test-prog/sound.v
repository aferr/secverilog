/* 
 * This file contains toy examples to test the soundness of the type
 * system of SecVerilog
 */
module sound();

reg[1:0] {L} low;
reg[1:0] {H} high;

// assume Par[0] = L, Par[1] = H, Par[2] = H, Par[3] = H
//
reg[1:0] {Par x} x;
reg[1:0] {Par y} y;

reg[2:0] {Par u} u;
reg[2:0] {Par v} v;

// this should work
always @(*) begin
	if (x == 0) begin
		low = 0;
	end
end

// this should fail
always @(*) begin
	if (high == 0) begin
		x = 1;
	end
end

// this should work
always @(*) begin
	if (low == 0) begin
		if (x == 0) begin
			y = x;
		end
	end
end

// this should work
always @(*) begin
	if (high == 0) begin
		if (x == 0) begin
			y = 1;
		end
		else begin
			y = 1;
		end
	end
	else begin
		y = 1;
	end
end

// this should work
always @(*) begin
	if (x == 0) begin
		y = 0;
	end
	else begin
		high = 1;
	end
end

// this should fail
always @(*) begin
	if (x == 1) begin
		x = high;
	end
end

// this should fail
always @(*) begin
	if (x == 1) begin
		x = x-1;
	end
end


endmodule
