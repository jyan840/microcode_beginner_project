; we need QF_UFBV for this proof
(set-logic QF_UFBV)

; insert the auto-generated code here
%%

; declare state variables s1
(declare-fun s1 () mult_s)

(assert (= (|mult_n s_o| s1)
		   (bvmul
		     (|mult_n a_i| s1)
		     (|mult_n b_i| s1))))

; is there such a model?
(check-sat)
;(get-model)
