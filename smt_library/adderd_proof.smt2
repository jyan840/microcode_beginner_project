; we need QF_UFBV for this proof
(set-logic QF_UFBV)

; insert the auto-generated code here

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



; declare state variables s1
(declare-const s0 state)
(declare-const s1 state)

(assert (= (a s0) #x05)) ; a = 5
(assert (= (b s0) #x06)) ; b = 6
(assert (= (clk s0) false))
(assert (= (clk s1) true))

(assert (adderd_t s0 s1)) ; s1 is the result of transition from s0

(assert (not (= (c s1) #x0b))) 

; is there such a model?
(check-sat)
(get-model)