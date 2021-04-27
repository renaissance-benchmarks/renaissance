(set-option :print-success true)
(set-logic QF_ABV)
(set-info :source |
Bit-vector benchmarks from Dawson Engler's tool contributed by Vijay Ganesh
(vganesh@stanford.edu).  Translated into SMT-LIB format by Clark Barrett using
CVC3.  |)
(set-info :smt-lib-version 2.0)
(set-info :category "industrial")
(set-info :status sat)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (bvslt ((_ sign_extend 24) (select a (_ bv1 32))) ((_ sign_extend 24) (select a (_ bv0 32)))))
(assert (let ((?v_0 (store (store a (_ bv1 32) (select a (_ bv0 32))) (_ bv0 32) ((_ extract 7 0) ((_ sign_extend 24) (select a (_ bv1 32))))))) (not (bvslt ((_ sign_extend 24) (select ?v_0 (_ bv2 32))) ((_ sign_extend 24) (select ?v_0 (_ bv1 32)))))))
(assert (let ((?v_0 (store (store a (_ bv1 32) (select a (_ bv0 32))) (_ bv0 32) ((_ extract 7 0) ((_ sign_extend 24) (select a (_ bv1 32))))))) (not (bvslt ((_ sign_extend 24) (select ?v_0 (_ bv3 32))) ((_ sign_extend 24) (select ?v_0 (_ bv2 32)))))))
(check-sat)
(exit)
