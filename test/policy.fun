(declare-fun epol (Int) Bool)

(assert (= (epol 0) false))
(assert (forall ((x Int)) (implies (not (= x 0)) (epol x) )))

(declare-fun Domain (Int) Label)
(assert
	(forall ((x Int) (y Int)) (implies (<= x y) (leq (Domain x) (Domain y)))))

(declare-fun Valid (Int Int) Label)
(assert
	(forall ((v Int) (x Int)) (ite (= v 0) (= (Valid v x) HIGH) (= (Valid v x) (Domain x)))))
	
(declare-fun miss (Int Int Int) Bool)
(assert (forall ((x Int) (y Int) (z Int))
	(ite (and (not (= x 0)) (<= y z)) (miss x y z) (not (miss x y z)))
	))
