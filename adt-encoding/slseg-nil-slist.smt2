(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun nxt (Int) Int)
(declare-fun key (Int) Int)

;; recdefs
(declare-fun slst (ListOfLoc) Bool)
(declare-fun slseg (ListOfLoc Int) Bool)

(assert (slst empty))
(assert (forall ((k Int))
	(= (slst (cons k empty)) (= (nxt k) nil))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc)) 
	(= (slst (cons k1 (cons k2 x))) 
	   (and (= (nxt k1) k2) (not (= k1 nil)) (<= (key k1) (key k2)) (slst (cons k2 x))))
))

(assert (forall ((y Int)) (slseg empty y)))
(assert (forall ((k Int) (y Int))
        (= (slseg (cons k empty) y)
           (and (not (= k nil)) (= (nxt k) y)))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc) (y Int))
        (= (slseg (cons k1 (cons k2 x)) y)
           (and (= (nxt k1) k2) (not (= k1 nil)) (<= (key k1) (key k2)) (slseg (cons k2 x) y)))
))

;; axioms
(assert (= (nxt nil) nil))

(declare-fun hx () ListOfLoc)
(declare-fun x () Int)
(declare-fun xs () ListOfLoc)
(declare-fun hy () ListOfLoc)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun ys () ListOfLoc)
(declare-fun c () ListOfLoc)
(declare-fun ret () Int)
(declare-fun rets () ListOfLoc)

;; uncommenting lemma goes through using cvc4+ig

;; ;; lemma
;; (assert (forall ((hx ListOfLoc) (hy ListOfLoc) (ys ListOfLoc) (y Int) (z Int))
;;         (=> (and (slseg hx y) (= hy (cons y ys))) (= (slst hx) (slst hy)))
;; ))

;; goal
(assert (not
        (=> (and (slseg hx y) (= hx (cons x xs)) (= hy (cons y empty)) (= y nil))
      	    (=> (ite (= x nil) (= ret nil) (= ret (nxt x)))
                (exists ((hret ListOfLoc))
                        (and (slst hret) (= hret (cons ret rets))))))
))

(check-sat)
