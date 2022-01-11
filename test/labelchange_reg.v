module labelchange_reg(
    input  clk,
    input  rst,
    input  data_in,
    output data_out
);

wire com {L} data_in;
wire seq {H} data_out;

always@(posedge clk) begin
    if(rst) data_out <= data_in;
    else data_out <= data_in;
end

endmodule
