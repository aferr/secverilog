; Speculation Label
; Spec(0 l) = unknown = l
; Spec(1 _) = misspec = TOP
(declare-fun SPEC (Int Int) Label)

(assert (forall ((x Int) (l Int)) (= (SPEC x l)
 (ite (= x 1) HIGH (LH l))
)))
