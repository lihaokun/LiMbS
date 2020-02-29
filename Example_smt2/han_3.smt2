(set-logic QF_NRA)
(set-info :smt-lib-version 2.0)
(set-option :produce-models true)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)

(assert (< (+ (* (- 4) (+ (* (* x1 x1) (* x2 x2)) (* (* x1 x1) (* 
x3 x3)) (* (* x2 x2) (* x3 x3)))) (* (+ (* x1 x1) (* 
x2 x2) (* x3 x3)) (+ (* x1 x1) (* x2 x2) (* x3 
x3)))) 0))
(check-sat)
(get-model)
