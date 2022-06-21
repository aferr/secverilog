(declare-fun epol (Int) Bool)

(assert (= (epol 0) false))
(assert (= (epol 1) true))
;(assert (forall ((x Int)) (implies (not (= x 0)) (= (epol x) True))))