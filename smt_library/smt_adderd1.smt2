; Define the abstract state sort
(declare-sort state 0)

; Inputs
(declare-fun a (state) (_ BitVec 8))
(declare-fun b (state) (_ BitVec 8))
(declare-fun clk (state) Bool)     

; Output register c
(declare-fun c (state) (_ BitVec 8))

; Combinational logic a + b
(define-fun result ((s state)) (_ BitVec 8)
  (bvadd (a s) (b s))) ; a + b

; State transition from result to output register
(define-fun adderd_t ((x state) (y state)) Bool
  (ite (and (not (clk x)) (clk y))   ; if !clk(x) and clk(y), which means it is the rising edge
       (= (c y) (result x))          
       (= (c y) (c x))))               