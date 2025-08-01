(* blackbox *)
(* smtlib2_module *)
module nerv_regs (clk, next_wr, wr_rd, raddr1, raddr2, next_rd, rdata1, rdata2);
	input clk, next_wr;
	input [4:0] wr_rd;
	input [4:0] raddr1;
	input [4:0] raddr2;
	input [31:0] next_rd;

    (* smtlib2_comb_expr = "(select (Array (_ BitVec 5) (_ BitVec 32)) raddr1)"*)
	output [31:0] rdata1;

    (* smtlib2_comb_expr = "(select (Array (_ BitVec 5) (_ BitVec 32)) raddr2)"*)
	output [31:0] rdata2;

	// reg [31:0] regs [0:31];

	// always @(posedge clk)
	// 	if (next_wr) regs[wr_rd] <= next_rd;

	assign rdata1 = regs[raddr1];
	assign rdata2 = regs[raddr2];
endmodule 