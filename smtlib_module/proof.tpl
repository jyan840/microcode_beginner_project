; we need QF_UFBV for this proof
(set-logic QF_UFBV)

; insert the auto-generated code here
%%

; declare state variables s1
(declare-fun s1 () test_s)

(assert (= (|test_n b_o| s1)
		   (bvand
		     (bvnot (|test_n a_i| s1))
		     (|test_n a_i| s1))
             #b00000000))

; is there such a model?
(check-sat)
;(get-model)
