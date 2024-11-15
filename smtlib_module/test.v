module test(a_i, b_o);
  input [7:0] a_i;
  output [7:0] b_o;
  wire [7:0] b;

  negate_submod
  negate_instance
  (
    .a(a_i),
	.b(b)
  );
  assign b_o = b + 1;
endmodule

(* blackbox *)
(* smtlib2_module *)
module negate_submod(a, b);
  input [7:0] a;
  (* smtlib2_comb_expr = "(bvnot a)" *)
  output [7:0] b;
  // assign b = ~a;
endmodule

