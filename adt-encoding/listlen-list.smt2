(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun nxt (Int) Int)
(declare-fun prv (Int) Int)

;; recdefs
(declare-fun lst (ListOfLoc) Bool)
(declare-fun lstlen_bool (ListOfLoc) Bool)
(declare-fun lstlen_int (ListOfLoc) Int)

(assert (lst empty))
(assert (forall ((k Int))
        (= (lst (cons k empty))
           (and (not (= k nil)) (= (nxt k) nil)))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (lst (cons k1 (cons k2 x)))
           (and (= (nxt k1) k2) (not (= k1 nil)) (lst (cons k2 x))))
))

(assert (lstlen_bool empty))
(assert (forall ((k Int))
        (= (lstlen_bool (cons k empty))
           (and (not (= k nil)) (= (nxt k) nil)))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (lstlen_bool (cons k1 (cons k2 x)))
           (and (= (nxt k1) k2) (not (= k1 nil)) (lstlen_bool (cons k2 x))))
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
        (=> (and (lstlen_bool hx) (= hx (cons x xs)))
	    (=> (ite (= x nil) (= ret nil) (= ret (nxt x)))
                (exists ((hret ListOfLoc))
                        (and (lst hret) (= hret (cons ret rets))))))
))

;; uncommenting below goes through using cvc4+ig (need lemma assumed)

;; ;; lemma
;; (assert (forall ((hx ListOfLoc)) (=> (lstlen_bool hx) (lst hx))))

;; ;; goal with explicit heaplets
;; (assert (not
;;         (=> (and (lstlen_bool hx) (= hx (cons x xs)))
;;             (=> (ite (= x nil) (= ret nil) (= ret (nxt x)))
;;                 (ite (= ret nil) (lst empty)
;;                       (and (lst xs) (= (head xs) ret)))))
;; ))

(check-sat)
