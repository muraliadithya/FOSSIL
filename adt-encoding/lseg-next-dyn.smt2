(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun nxt (Int) Int)
(declare-fun key (Int) Int)
(declare-fun yc () ListOfLoc)
(declare-fun zc () ListOfLoc)

(define-fun nxt_p ((x Int)) Int
  (ite (= x (head yc)) (head zc) (nxt x))
)

;; recdefs
(declare-fun lsegy (ListOfLoc) Bool)
(declare-fun lsegz (ListOfLoc) Bool)
(declare-fun lsegy_p (ListOfLoc) Bool)
(declare-fun lsegz_p (ListOfLoc) Bool)

(assert (lsegy empty))
(assert (forall ((k Int))
        (= (lsegy (cons k empty))
           (and (not (= k nil)) (= (nxt k) (head yc))))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (lsegy (cons k1 (cons k2 x)))
           (and (= (nxt k1) k2) (not (= k1 nil)) (lsegy (cons k2 x))))
))

(assert (lsegz empty))
(assert (forall ((k Int))
        (= (lsegz (cons k empty))
           (and (not (= k nil)) (= (nxt k) (head zc))))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (lsegz (cons k1 (cons k2 x)))
           (and (= (nxt k1) k2) (not (= k1 nil)) (lsegz (cons k2 x))))
))

(assert (lsegy_p empty))
(assert (forall ((k Int))
        (= (lsegy_p (cons k empty))
           (and (not (= k nil)) (= (nxt_p k) (head yc))))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (lsegy_p (cons k1 (cons k2 x)))
           (and (= (nxt_p k1) k2) (not (= k1 nil)) (lsegy_p (cons k2 x))))
))

(assert (lsegz_p empty))
(assert (forall ((k Int))
        (= (lsegz_p (cons k empty))
           (and (not (= k nil)) (= (nxt_p k) (head zc))))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (lsegz_p (cons k1 (cons k2 x)))
           (and (= (nxt_p k1) k2) (not (= k1 nil)) (lsegz_p (cons k2 x))))
))

(declare-fun hx () ListOfLoc)
(declare-fun x () Int)
(declare-fun xs () ListOfLoc)
(declare-fun k () Int)

;; uncommenting lemma goes through using cvc4+ig

;; ;; lemma
;; (assert (forall ((hx ListOfLoc))
;;         (=> (lsegy hx) (lsegz_p hx)) 
;; ))

;; goal
(assert (not
        (=> (and (lsegy hx) (= hx (cons x xs)))
	    (=> (not (= (key x) k))
                (lsegz_p hx)))
))

(check-sat)