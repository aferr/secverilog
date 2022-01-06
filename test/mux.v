module Two_Input_Mux
(
	input {D1}          in1,
	input {D2}          in2,
	input {L}           sel,
	output {Domain sel} out
);

reg	{Domain sel} out;

always @ (*) begin
	if (sel == 1'b0)
		out = in1;
	else
		out = in2;
end
endmodule
