/* 
 * This example implements a finite state machine with 3 states, where
 * state 0 is L and states 2, 3 are H.
 * A timer controls the switch between L and H states every 10 cycles. 
 */
module deptype(clk, timer, data, out);

input {L} clk;
input[15:0] {L} timer; // 16-bit timer
input[15:0] {H} data;  // 16-bit secret data

output reg [15:0] {L} out;

// current mode, 0 for L state 1; 1 for H states 2 and 3
reg[1:0] {L} mode;

// assume Par[0] = L, Par[1] = H, Par[2] = H
reg[1:0] {Par cur_state} cur_state;
reg[1:0] {Par next_state} next_state;
reg[15:0] {L} cur_timer;
reg[15:0] {L} next_timer;

initial begin  // initialization
    mode = 0;
    cur_state = 0;
    cur_timer = 10;
end
    
always @(posedge clk) begin
    cur_state <= next_state;
    cur_timer <= next_timer;
end

always @(negedge clk) begin
    if (cur_timer == 0) begin // pc = L, switch states
        mode <= ~mode;
        next_timer <= 10;
        if (mode == 0) begin // pc = L
            next_state <= 1;
        end
        else begin
            next_state <= 0;
        end
    end
    else begin
        next_timer <= cur_timer - 1;
        case (cur_state)
        0: begin // pc = Par[cur_state] = L 
            out <= 15;
        end
        1: begin // pc = Par[cur_state] = H
            // jump to state 2 only when secret "data" is not zero
            if (data != 0) begin    
                next_state <= 2;
            end
        end
        2: begin // pc = Par[cur_state] = H
            if (data != 0) begin    
               next_state <= 1;
            end
        end
        endcase
    end
end

endmodule
