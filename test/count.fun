; Domain(0)=D1, Domain(1)=D2
(declare-fun Domain (Int) Label)
(assert
	(forall ((x Int) (y Int)) (implies (<= x y) (leq (Domain x) (Domain y)))))
;(assert (= (Domain 0) D1))
;(assert (= (Domain 1) D2))


