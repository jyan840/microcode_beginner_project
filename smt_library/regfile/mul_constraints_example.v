(* smtlib2_module *)
module smtlib_constraint(
    input [7:0] a,
    input [7:0] b,
    input [7:0] x,
    // We can combine multiple constraints using `and`
    (* smtlib2_comb_expr = "
        (and
            (= x (bvmul a b))
            (= x (bvadd a b))
        )
    " *)
    output valid
);
endmodule

module smtlib_wrapper(
    input [7:0] a,
    input [7:0] b,
    output [7:0] x
);

    wire valid;

    // We create a symbolic output value
    assign x = $anyseq;

    // Check whether the output value fulfills our smtlib2 constraint
    smtlib_constraint constraint(.a(a), .b(b), .x(x), .valid(valid));

    // And add an assumption so FV will only consider output values that do
    // fulfill the constraint
    always @* enforce_smtlib_constraint: assume (valid);
endmodule