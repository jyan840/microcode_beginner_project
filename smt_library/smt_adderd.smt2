; SMT-LIBv2 description generated by Yosys 0.46+124 (git sha1 d1695ad99, g++ 15.0.0 -fPIC -O3)
; yosys-smt2-module adderd
(declare-sort |adderd_s| 0)
(declare-fun |adderd_is| (|adderd_s|) Bool)
(declare-fun |adderd#0| (|adderd_s|) (_ BitVec 8)) ; \a
; yosys-smt2-input a 8
; yosys-smt2-witness {"offset": 0, "path": ["\\a"], "smtname": "a", "smtoffset": 0, "type": "input", "width": 8}
(define-fun |adderd_n a| ((state |adderd_s|)) (_ BitVec 8) (|adderd#0| state))
(declare-fun |adderd#1| (|adderd_s|) (_ BitVec 8)) ; \b
; yosys-smt2-input b 8
; yosys-smt2-witness {"offset": 0, "path": ["\\b"], "smtname": "b", "smtoffset": 0, "type": "input", "width": 8}
(define-fun |adderd_n b| ((state |adderd_s|)) (_ BitVec 8) (|adderd#1| state))
; yosys-smt2-witness {"offset": 0, "path": ["\\c"], "smtname": 2, "smtoffset": 0, "type": "reg", "width": 8}
(declare-fun |adderd#2| (|adderd_s|) (_ BitVec 8)) ; \c
; yosys-smt2-output c 8
; yosys-smt2-register c 8
(define-fun |adderd_n c| ((state |adderd_s|)) (_ BitVec 8) (|adderd#2| state))
(declare-fun |adderd#3| (|adderd_s|) Bool) ; \clk
; yosys-smt2-input clk 1
; yosys-smt2-clock clk posedge
; yosys-smt2-witness {"offset": 0, "path": ["\\clk"], "smtname": "clk", "smtoffset": 0, "type": "posedge", "width": 1}
; yosys-smt2-witness {"offset": 0, "path": ["\\clk"], "smtname": "clk", "smtoffset": 0, "type": "input", "width": 1}
(define-fun |adderd_n clk| ((state |adderd_s|)) Bool (|adderd#3| state))
(define-fun |adderd#4| ((state |adderd_s|)) (_ BitVec 8) (bvadd (|adderd#0| state) (|adderd#1| state))) ; $0\c[7:0]
(define-fun |adderd_a| ((state |adderd_s|)) Bool true)
(define-fun |adderd_u| ((state |adderd_s|)) Bool true)
(define-fun |adderd_i| ((state |adderd_s|)) Bool true)
(define-fun |adderd_h| ((state |adderd_s|)) Bool true)
(define-fun |adderd_t| ((state |adderd_s|) (next_state |adderd_s|)) Bool 
  (= (|adderd#4| state) (|adderd#2| next_state)) ; $procdff$3 \c
) ; end of module adderd
; yosys-smt2-topmod adderd
; end of yosys output
