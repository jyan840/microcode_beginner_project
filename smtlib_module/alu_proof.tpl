; we need QF_UFBV for this proof
(set-logic QF_UFBV)

; insert the auto-generated code here
%%

; declare state variables s1
(declare-fun s1 () alu_s)

(assert (= (|alu_n result| s1)
		   (ite
		    (= (|alu_n op| s1) #b1)
		    (bvmul
		     (|alu_n a| s1)
		     (|alu_n b| s1))
		    (bvadd
		     (|alu_n a| s1)
		     (|alu_n b| s1)))))

; is there such a model?
(check-sat)
;(get-model)
