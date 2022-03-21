(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun nxt (Int) Int)
(declare-fun key (Int) Int)

;; recdefs
(declare-fun lst (ListOfLoc) Bool)
(declare-fun slst (ListOfLoc) Bool)

(assert (lst empty))
(assert (forall ((k Int) (x ListOfLoc)) 
        (= (lst (cons k empty))
	   (= (nxt k) nil))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc)) 
	(= (lst (cons k1 (cons k2 x))) 
	   (and (= (nxt k1) k2) (lst (cons k2 x))))
))

(assert (slst empty))
(assert (forall ((k Int) (x ListOfLoc)) 
	(= (slst (cons k empty)) (= (nxt k) nil))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc)) 
	(= (slst (cons k1 (cons k2 x))) 
	   (and (= (nxt k1) k2) (<= (key k1) (key k2)) (slst (cons k2 x))))
))

(declare-fun hx () ListOfLoc)
(declare-fun x () Int)
(declare-fun xs () ListOfLoc)
(declare-fun ret () Int)
(declare-fun rets () ListOfLoc)

;; faithful encoding

;; goal
(assert (not
        (=> (and (slst hx) (= hx (cons x xs)))
            (=> (ite (= x nil) (= ret nil) (= ret (nxt x)))
                (exists ((hret ListOfLoc))
                        (and (lst hret) (= hret (cons ret rets))))))
))

;; uncommenting below goes through using cvc4+ig (do not need to assume lemma)

;; ;; goal with explicit heaplets
;; (assert (not
;;         (=> (and (slst hx) (= hx (cons x xs)))
;;             (=> (ite (= x nil) (= ret nil) (= ret (nxt x)))
;;                  (ite (= ret nil) (lst empty)
;;                      (and (slst xs) (= (head xs) ret)))))
;; ))

(check-sat)
