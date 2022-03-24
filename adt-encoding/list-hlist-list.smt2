(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun nxt (Int) Int)
(declare-fun key (Int) Int)

;; recdefs
(declare-fun lst (ListOfLoc) Bool)
(declare-fun hlst (ListOfLoc) (Set Int))

(assert (lst empty))
(assert (forall ((k Int))
        (= (lst (cons k empty))
           (and (not (= k nil)) (= (nxt k) nil)))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (lst (cons k1 (cons k2 x)))
           (and (= (nxt k1) k2) (not (= k1 nil)) (lst (cons k2 x))))
))

(assert (= (hlst empty) (as emptyset (Set Int))))
(assert (forall ((k Int))
        (=> (and (not (= k nil)) (= (nxt k) nil))
            (= (hlst (cons k empty)) (singleton k)))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (=> (and (= (nxt k1) k2) (not (= k1 nil)))
            (= (hlst (cons k1 (cons k2 x))) (insert k1 (hlst (cons k2 x)))))
))

(declare-fun hx () ListOfLoc)
(declare-fun x () Int)
(declare-fun xs () ListOfLoc)
(declare-fun hy () ListOfLoc)
(declare-fun y () Int)
(declare-fun ys () ListOfLoc)
(declare-fun k () Int)

;; uncommenting lemma goes through using cvc4+ig

;; ;; lemma
;; (assert (forall ((hx ListOfLoc) (hy ListOfLoc) (y Int) (ys ListOfLoc))
;;         (=> (and (lst hx) (= hy (cons y ys)) (member y (hlst hx)))
;;             (lst hy))
;; ))

;; goal
(assert (not
        (=> (and (lst hx) (= hx (cons x xs)) (not (= (key x) k)) 
                 (= hy (cons y ys)) (member y (hlst hx)))
            (exists ((hret ListOfLoc) (hrets ListOfLoc))
                    (and (lst hret) (= hret (cons y hrets)))))
))

(check-sat)
