; we need QF_UFBV for this proof
(set-logic QF_UFBV)

; insert the auto-generated code here


; Inputs
(declare-fun a () (_ BitVec 8))
(declare-fun b () (_ BitVec 8))

; Output - Purely Combinational Logic
(define-fun c () (_ BitVec 8)
    (bvadd a b))

    

(assert (= a #x03)) ; a = 3
(assert (= b #x09)) ; b = 9

(assert (not (= c #x0c))) 

; is there such a model?
(check-sat)
(get-model)


