(set-logic QF_NRA)
(set-info :smt-lib-version 2.0)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(assert (< (+ (* (- 4) (+ (* (* x1 x1) (* x2 x2)) (* (* x1 x1) (* 
x5 x5)) (* (* x2 x2) (* x3 x3)) (* (* x3 x3) (* x4 
x4)) (* (* x4 x4) (* x5 x5)))) (* (+ (* x1 x1) (* x2 
x2) (* x3 x3) (* x4 x4) (* x5 x5)) (+ (* x1 x1) (* 
x2 x2) (* x3 x3) (* x4 x4) (* x5 x5)))) 0))
(check-sat)
