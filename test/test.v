module test(clk, timer, data, out);

input clk;
input [15:0] timer; // 16-bit timer
input [15:0] data;  // 16-bit data

output reg [15:0] out;

reg [1:0] cur_state;
reg [1:0] next_state;
reg [15:0] cur_timer;
reg [15:0] next_timer;

initial begin  // initialization
	cur_state = 0;
end
	
always @(posedge clk) begin
	cur_state <= next_state;
	cur_timer <= next_timer;
end

always @(*) begin
	case(cur_state)
		0: begin
			if (timer) begin
				next_state <= 1;
				next_timer <= timer;
			end
			else begin
				next_state <= 0;
				next_timer <=0;
				out <= 15;
			end
		end
		
		1: begin
			if (cur_timer == 0) begin
				next_state <= 0;
			end
			else begin
				if (data) begin
					next_state <= 2;
				end
				next_timer <= cur_timer - 1;
			end
		end
		
		2: begin
			if (cur_timer == 0) begin
				next_state <= 0;
			end
			else begin
				if (data) begin
					next_state <= 1;
				end
				next_timer <= cur_timer - 1;
			end
		end
	endcase
end

endmodule
