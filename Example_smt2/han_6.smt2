(set-logic QF_NRA)
(set-info :smt-lib-version 2.0)
(declare-fun x1 () Real)
(declare-fun x2 () Real)
(declare-fun x3 () Real)
(declare-fun x4 () Real)
(declare-fun x5 () Real)
(declare-fun x6 () Real)
(assert (< (+ (* (- 4) (+ (* (* x1 x1) (* x2 x2)) (* (* x1 x1) (* 
x6 x6)) (* (* x2 x2) (* x3 x3)) (* (* x3 x3) (* x4 
x4)) (* (* x4 x4) (* x5 x5)) (* (* x5 x5) (* x6 
x6)))) (* (+ (* x1 x1) (* x2 x2) (* x3 x3) (* x4 
x4) (* x5 x5) (* x6 x6)) (+ (* x1 x1) (* x2 x2) (* 
x3 x3) (* x4 x4) (* x5 x5) (* x6 x6)))) 0))
(check-sat)
