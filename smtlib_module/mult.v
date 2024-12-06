(* blackbox *)
(* smtlib2_module *)
module mult #(parameter a_p = 128,
             parameter b_p = 128)
  (a_i, b_i, s_o);

  input [a_p-1:0] a_i;
  input [b_p-1:0] b_i;
  (* smtlib2_comb_expr = "(bvmul a_i b_i)" *)
  // output [(a_p + b_p)-1:0] s_o;
  output [a_p-1:0] s_o;

  assign s_o = a_i * b_i;

endmodule

