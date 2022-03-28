(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((Execution (cons (head Int) (tail Execution)) (start))))

;; unint functions
(declare-fun nil () Int)
(declare-fun c () Int)
(declare-fun prv_cfg (Int) Int)
(declare-fun nxt (Int) Int)
(declare-fun v1 (Int) Int)
(declare-fun v2 (Int) Int)

;; recdefs
(declare-fun reach_pgm (Execution) Bool)

(define-fun cond ((x Int)) Bool
  (not (= (v1 (prv_cfg x)) c))
)

(define-fun assign ((x Int)) Bool
  (and (= (v1 x) (nxt (v1 (prv_cfg x))))
       (ite (not (= (v2 (prv_cfg x)) c))
            (= (v2 x) (nxt (v2 (prv_cfg x))))
            (= (v2 x) (v2 (prv_cfg x)))))
)

(define-fun body ((x Int)) Bool
  (and (cond x) (assign x))
)

(assert (reach_pgm start))
(assert (forall ((k Int))
        (= (reach_pgm (cons k start))
           (and (not (= k nil)) (= (prv_cfg k) nil) (body k)))
))
(assert (forall ((k1 Int) (k2 Int) (x Execution))
        (= (reach_pgm (cons k1 (cons k2 x)))
           (and (not (= k1 nil)) (= (prv_cfg k1) k2) (body k1) (reach_pgm (cons k2 x))))
))

;; precondition
(assert (= (v1 (head start)) (v2 (head start))))

(declare-fun hx () Execution)
(declare-fun x () Int)
(declare-fun xs () Execution)

;; uncommenting lemma goes through using cvc4+ig

;; ;; lemma
;; (assert (forall ((hx Execution) (x Int) (xs Execution))
;;         (=> (and (reach_pgm hx) (= hx (cons x xs)))
;;             (= (v1 x) (v2 x)))
;; ))

;; goal
(assert (not
        (=> (and (reach_pgm hx) (= hx (cons x xs)))
	    (=> (= (v1 x) nil)
                (or (= (v2 x) nil) (= (v2 x) c))))
))

(check-sat)
