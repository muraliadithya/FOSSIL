(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun nxt (Int) Int)
(declare-fun prv (Int) Int)

;; recdefs
(declare-fun lst (ListOfLoc) Bool)
(declare-fun even_lst (ListOfLoc) Bool)
(declare-fun odd_lst (ListOfLoc) Bool)

(assert (lst empty))
(assert (forall ((k Int))
        (= (lst (cons k empty))
           (and (not (= k nil)) (= (nxt k) nil)))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (lst (cons k1 (cons k2 x)))
           (and (= (nxt k1) k2) (not (= k1 nil)) (lst (cons k2 x))))
))

(assert (even_lst empty))
(assert (forall ((k Int)) (not (even_lst (cons k empty)))))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (even_lst (cons k1 (cons k2 x)))
           (and (= (nxt k1) k2) (not (= k1 nil)) (odd_lst (cons k2 x))))
))

(assert (not (odd_lst empty)))
(assert (forall ((k Int))
        (= (odd_lst (cons k empty))
           (and (not (= k nil)) (= (nxt k) nil)))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (odd_lst (cons k1 (cons k2 x)))
           (and (= (nxt k1) k2) (not (= k1 nil)) (even_lst (cons k2 x))))
))

;; axioms
(assert (= (nxt nil) nil))

(declare-fun hx () ListOfLoc)
(declare-fun x () Int)
(declare-fun xs () ListOfLoc)
(declare-fun ret () Int)
(declare-fun rets () ListOfLoc)

;; faithful encoding

;; goal
(assert (not
        (=> (and (odd_lst hx) (= hx (cons x xs)))
	    (=> (ite (= x nil) (= ret nil) (= ret (nxt x)))
                (exists ((hret ListOfLoc))
                        (and (lst hret) (= hret (cons ret rets))))))
))

;; uncommenting below goes through using cvc4+ig (need lemma assumed)

;; ;; lemma
;; (assert (forall ((hx ListOfLoc)) (=> (odd_lst hx) (lst hx))))

;; ;; goal with explicit heaplets
;; (assert (not
;;         (=> (and (odd_lst hx) (= hx (cons x xs)))
;;             (=> (ite (= x nil) (= ret nil) (= ret (nxt x)))
;;                 (ite (= ret nil) (lst empty)
;;                      (and (lst xs) (= (head xs) ret)))))
;; ))

(check-sat)
