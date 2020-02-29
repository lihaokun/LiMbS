(set-logic QF_NRA)
(set-info :smt-lib-version 2.0)
(set-option :produce-models true)
(declare-fun a () Real)
(declare-fun b () Real)
(declare-fun c () Real)
(declare-fun d () Real)
(declare-fun e () Real)
(declare-fun f () Real)

(assert (< (+ (* (- 1) (+ (* (- 1) (+ (* (- 1) e f) c (* c (* f f))) b) (* (+ 1 (* 
(+ (* (- 2) e f) c (* c (* f f))) c) (* e e)) a) (* (- 1) d e) (* c d 
f)) (+ (* (- 1) (+ 1 (* f f)) b) (* (+ (* (- 1) e f) c (* c (* f f))) 
a) (* d f)) a b) (* (+ 1 (* (* (+ (* (- 1) a c) b) (+ (* (- 1) a c) 
b)) (* f f)) (* (+ (* (- 1) a c) b) (+ (* (- 1) d) (* a e)) 2 f) (* 
(+ (* (+ 1 (* c c) (* e e)) a) (* (- 2) (+ (* b c) (* d e)))) a) (* b 
b) (* d d)) (+ (* (- 1) e f) c (* c (* f f))) (+ (* a b) c))) 0))
(check-sat)
(get-model)