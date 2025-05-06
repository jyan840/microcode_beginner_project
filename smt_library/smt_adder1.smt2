; Inputs
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))

; Output - Purely Combinational Logic
(define-fun c () (_ BitVec 8)
    (bvadd a b))