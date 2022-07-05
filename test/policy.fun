(declare-fun epol (Int) Bool)

(assert (= (epol 0) false))
(assert (forall ((x Int)) (implies (not (= x 0)) (epol x) )))

(declare-fun miss (Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (z Int))
	(ite (and (not (= x 0)) (<= y z)) (miss x y z) (not (miss x y z)))
	))

(declare-fun Domain (Int) Label)
(assert
	(forall ((x Int) (y Int)) (implies (<= x y) (leq (Domain x) (Domain y)))))
; Bottom bit (i.e., even integers) is the valid bit, if its zero then treat as TOP
(assert (forall ((x Int)) (implies (= (mod x 2) 0) (= HIGH (Domain x)))))
