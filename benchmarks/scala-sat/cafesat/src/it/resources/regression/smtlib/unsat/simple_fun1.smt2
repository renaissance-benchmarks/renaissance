(set-logic QF_UF)
(declare-sort U 0)
(declare-fun g (U) U)
(declare-fun h (U) U)
(declare-fun a () U)
(declare-fun b () U)
(assert 
  (and 
    (= (g (h a)) b) 
    (not (= (g (h a)) b))))
(check-sat)
(exit)
