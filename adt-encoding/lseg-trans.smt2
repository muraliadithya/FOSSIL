(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun nxt (Int) Int)

;; recdefs
(declare-fun lst (ListOfLoc) Bool)
(declare-fun lseg (ListOfLoc Int) Bool)

(assert (lst empty))
(assert (forall ((k Int))
        (= (lst (cons k empty))
           (and (not (= k nil)) (= (nxt k) nil)))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (lst (cons k1 (cons k2 x)))
           (and (= (nxt k1) k2) (not (= k1 nil)) (lst (cons k2 x))))
))

(assert (forall ((y Int)) (lseg empty y)))
(assert (forall ((k Int) (y Int))
        (= (lseg (cons k empty) y)
           (and (not (= k nil)) (= (nxt k) y)))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc) (y Int))
        (= (lseg (cons k1 (cons k2 x)) y)
           (and (= (nxt k1) k2) (not (= k1 nil)) (lseg (cons k2 x) y)))
))

(declare-fun hx () ListOfLoc)
(declare-fun x () Int)
(declare-fun xs () ListOfLoc)
(declare-fun hy () ListOfLoc)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun ys () ListOfLoc)
(declare-fun c () ListOfLoc)

;; lemma
(assert (forall ((hx ListOfLoc) (hy ListOfLoc) (ys ListOfLoc) (y Int) (z Int))
        (=> (and (lseg hx y) (= hy (cons y ys)) (lseg hy z)) (lseg hx z))
))

;; ;; goal
;; (assert (not
;;         (=> (and (lseg hx y) (= hx (cons x xs)) (= hy (cons y (cons z ys))))
;;             (=> (and (not (= hx c)) (lseg hx z))
;;                 (exists ((hret ListOfLoc))
;;                         (and (lst hret) (= hret (cons z ys))))))
;; ))

;; goal
(assert (not
        (=> (and (lseg hx y) (= hx (cons x xs)) (= hy (cons y (cons z ys))))
	    (=> (and (not (= hx c)) (lseg hx z))
                (ite (= z nil) (lst empty)
                     (and (lst ys) (= (head ys) z)))))
))

(check-sat)
