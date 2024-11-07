#lang rosette/safe
Processing module `\bsg_adder_ripple_carry`.
(struct bsg_adder_ripple_carry_Inputs (a_i b_i) #:transparent
  ; a_i (bitvector 16)
  ; b_i (bitvector 16)
)
(struct bsg_adder_ripple_carry_Outputs (s_o c_o) #:transparent
  ; s_o (bitvector 16)
  ; c_o (bitvector 1)
)
(struct bsg_adder_ripple_carry_State () #:transparent)
(define (bsg_adder_ripple_carry inputs state)
  (let ((a_i (bsg_adder_ripple_carry_Inputs-a_i inputs))) ; (bitvector 16)
  (let ((n1 (zero-extend a_i (bitvector 17)))) ; (bitvector 17)
  (let ((b_i (bsg_adder_ripple_carry_Inputs-b_i inputs))) ; (bitvector 16)
  (let ((n3 (zero-extend b_i (bitvector 17)))) ; (bitvector 17)
  (let
    (($add$_Users_katzyan_Projects_Researches_microcode_beginner_project_verilog_to_rosette_bsg_adder_ripple_carry.v_40$1$_Y
      (bvadd n1 n3))) ; (bitvector 17)
  (let
    ((s_o
      (extract
        15
        0
        $add$_Users_katzyan_Projects_Researches_microcode_beginner_project_verilog_to_rosette_bsg_adder_ripple_carry.v_40$1$_Y))) ; (bitvector 16)
  (let
    ((c_o
      (extract
        16
        16
        $add$_Users_katzyan_Projects_Researches_microcode_beginner_project_verilog_to_rosette_bsg_adder_ripple_carry.v_40$1$_Y))) ; (bitvector 1)
  (cons
    (bsg_adder_ripple_carry_Outputs
      s_o ; s_o
      c_o ; c_o
    )
    (bsg_adder_ripple_carry_State))))))))))
(define bsg_adder_ripple_carry_initial
  (bsg_adder_ripple_carry_State))
Processing module `\top`.
(struct top_Inputs (a_i b_i) #:transparent
  ; a_i (bitvector 16)
  ; b_i (bitvector 16)
)
(struct top_Outputs (s_o c_o) #:transparent
  ; s_o (bitvector 16)
  ; c_o (bitvector 1)
)
(struct top_State () #:transparent)
(define (top inputs state)
  (let ((s_o s_o)) ; (bitvector 16)
  (let ((c_o c_o)) ; (bitvector 1)
  (cons
    (top_Outputs
      s_o ; s_o
      c_o ; c_o
    )
    (top_State)))))
(define top_initial
  (top_State))