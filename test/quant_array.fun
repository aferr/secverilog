(declare-fun LH_ARRAY ((Array Int Int) Int) Label)

(assert (forall ((x (Array Int Int)) (y Int))
	(= (LH_ARRAY x y) (LH (select x y)))))