; Define the abstract state sort
(declare-sort state 0)

; input
(declare-fun clk (state) Bool)
(declare-fun next_wr (state) Bool)
(declare-fun raddr1 (state) (_ BitVec 5))
(declare-fun raddr2 (state) (_ BitVec 5))
(declare-fun wr_rd (state) (_ BitVec 5))
(declare-fun next_rd (state) (_ BitVec 32))

; output
(define-fun rdata1 (s state) (_ BitVec 32) (select (regfile s) (raddr1 s)))
(define-fun rdata2 (s state) (_ BitVec 32) (select (regfile s) (raddr2 s)))

(declare-fun regfile (state) (Array (_ BitVec 5) (_ BitVec 32)))
(define-fun regfile_store (s state) (Array (_ BitVec 5) (_ BitVec 32)) (ite (= (next_wr state) #b0) (regfile s)) (store (regfile s) (wr_rd s) (next_rd s)))

; state transition
(define-fun smt-regfile-t ((x state) (y state)) Bool
  (ite (and (not (clk x)) (clk y))
    (= (regfile y) (regfile_store x))
    (= (regfile y) (regfile x))))



