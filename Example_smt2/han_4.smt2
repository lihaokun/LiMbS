(set-logic QF_NRA)
(set-info :smt-lib-version 2.0)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(assert (< (+ (* (- 4) (+ (* (* x1 x1) (* x2 x2)) (* (* x1 x1) (* 
x4 x4)) (* (* x2 x2) (* x3 x3)) (* (* x3 x3) (* x4 
x4)))) (* (+ (* x1 x1) (* x2 x2) (* x3 x3) (* x4 
x4)) (+ (* x1 x1) (* x2 x2) (* x3 x3) (* x4 x4)))) 0))
(check-sat)