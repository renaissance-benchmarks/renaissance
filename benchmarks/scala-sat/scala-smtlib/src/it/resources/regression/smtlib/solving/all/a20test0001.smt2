(set-option :print-success true)
(set-logic QF_ABV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.  |)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun x () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun y () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= (concat (_ bv0 30) ((_ extract 2 1) (select x (_ bv0 32)))) (_ bv2 32)))
(assert (not (not (= ((_ extract 3 3) (select y (_ bv0 32))) (_ bv0 1)))))
(check-sat)
(exit)
