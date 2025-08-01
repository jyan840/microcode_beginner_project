; we need QF_UFBV for this proof
(set-logic QF_AUFBV)

; insert the auto-generated code here

; Define the abstract state sort
(declare-sort state 0)

; input
(declare-fun clk (state) Bool)
(declare-fun next_wr (state) Bool)
(declare-fun raddr1 (state) (_ BitVec 5))
(declare-fun raddr2 (state) (_ BitVec 5))
(declare-fun wr_rd (state) (_ BitVec 5))
(declare-fun next_rd (state) (_ BitVec 32))

(declare-fun regfile (state) (Array (_ BitVec 5) (_ BitVec 32)))

; output
(define-fun rdata1 ((s state)) (_ BitVec 32) (select (regfile s) (raddr1 s)))
(define-fun rdata2 ((s state)) (_ BitVec 32) (select (regfile s) (raddr2 s)))

(define-fun regfile_store ((s state)) (Array (_ BitVec 5) (_ BitVec 32)) (ite (= (next_wr s) false) (regfile s) (store (regfile s) (wr_rd s) (next_rd s))))

; state transition
(define-fun smt-regfile-t ((x state) (y state)) Bool
  (ite (and (not (clk x)) (clk y))
    (= (regfile y) (regfile_store x))
    (= (regfile y) (regfile x))))

; declare state variables s1
(declare-fun s0 () state)
(declare-fun s1 () state)

(assert (= (clk s0) false))
(assert (= (clk s1) true))
(assert (smt-regfile-t s0 s1))

(assert (not (= (ite (next_wr s0) (next_rd s0) (select (regfile s0) (wr_rd s0))) (select (regfile s1) (wr_rd s0)))))
(assert (not (= (select (regfile s0) (raddr1 s0)) (rdata1 s0))))
(assert (not (= (select (regfile s0) (raddr2 s0)) (rdata2 s0))))

; is there such a model?
(check-sat)
;(get-model)
