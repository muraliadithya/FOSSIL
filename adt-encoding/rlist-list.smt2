(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun nxt (Int) Int)
(declare-fun red (Int) Bool)
(declare-fun black (Int) Bool)

;; recdefs
(declare-fun lst (ListOfLoc) Bool)
(declare-fun rlst (ListOfLoc) Bool)

(assert (lst empty))
(assert (forall ((k Int))
        (= (lst (cons k empty))
           (and (not (= k nil)) (= (nxt k) nil)))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (lst (cons k1 (cons k2 x)))
           (and (= (nxt k1) k2) (not (= k1 nil)) (lst (cons k2 x))))
))

(assert (rlst empty))
(assert (forall ((k Int))
        (= (rlst (cons k empty))
           (and (not (= k nil)) (= (nxt k) nil) (black k)))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (rlst (cons k1 (cons k2 x)))
           (and (= (nxt k1) k2) (not (= k1 nil)) (rlst (cons k2 x))
                (or (and (red k1) (not (black k1)) (black k2) (not (red k2)))
                    (and (black k1) (not (red k1)) (red k2) (not (black k2))))))
))

(declare-fun hx () ListOfLoc)
(declare-fun x () Int)
(declare-fun xs () ListOfLoc)
(declare-fun ret () Int)
(declare-fun rets () ListOfLoc)

;; faithful encoding

;; goal
(assert (not
        (=> (and (rlst hx) (= hx (cons x xs)))
            (=> (ite (= x nil) (= ret nil) (= ret (nxt x)))
                 (exists ((hret ListOfLoc))
                         (and (lst hret) (= hret (cons ret rets))))))
))

;; uncommenting below goes through using cvc4+ig (need lemma assumed)

;; ;; lemma
;; (assert (forall ((hx ListOfLoc)) (=> (rlst hx) (lst hx))))

;; ;; goal with explicit heaplets
;; (assert (not
;;         (=> (and (rlst hx) (= hx (cons x xs)))
;;             (=> (ite (= x nil) (= ret nil) (= ret (nxt x)))
;;                 (ite (= ret nil) (lst empty)
;;                      (and (lst xs) (= (head xs) ret)))))
;; ))

(check-sat)
