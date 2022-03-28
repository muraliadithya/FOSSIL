(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun nxt (Int) Int)
(declare-fun key (Int) Int)

;; recdefs
(declare-fun lseg (ListOfLoc Int) Bool)

(assert (forall ((y Int)) (lseg empty y)))
(assert (forall ((k Int) (y Int))
        (= (lseg (cons k empty) y)
           (and (not (= k nil)) (= (nxt k) y)))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc) (y Int))
        (= (lseg (cons k1 (cons k2 x)) y)
           (and (= (nxt k1) k2) (not (= k1 nil)) (lseg (cons k2 x) y)))
))

;; ;; axioms
;; (assert (= (nxt nil) nil))

(declare-fun hx () ListOfLoc)
(declare-fun x () Int)
(declare-fun xs () ListOfLoc)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun k () Int)

;; uncommenting lemma goes through using cvc4+ig

;; ;; lemma
;; (assert (forall ((hx ListOfLoc) (hy ListOfLoc) (hz ListOfLoc) (ys ListOfLoc) (zs ListOfLoc) 
;;                  (y Int) (z Int))
;;         (=> (and (lseg hx y) (lseg hx z))
;;             (or (and (= hy (cons y ys)) (lseg hy z))
;;                 (and (= hz (cons z zs)) (lseg hz y))))
;; ))

;; goal
(assert (not
        (=> (and (lseg hx y) (lseg hx z) (= hx (cons x xs)))
	    (=> (not (= (key x) k))
                (exists ((hret ListOfLoc) (hrets ListOfLoc))
                        (or (and (lseg hret z) (= hret (cons (nxt y) hrets)))
                            (and (lseg hret y) (= hret (cons (nxt z) hrets)))))))
))

(check-sat)
