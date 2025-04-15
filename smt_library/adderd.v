parameter WIDTH = 8;

module adderd (
    input clk,
    input  [WIDTH-1:0] a,
    input  [WIDTH-1:0] b,
    output reg [WIDTH-1:0] c
);
    always @(posedge clk) begin
        c <= a + b;
    end
endmodule