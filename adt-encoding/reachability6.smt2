;; preamble
(define-fun iff ((b1 Bool) (b2 Bool)) Bool
  (and (=> b1 b2) (=> b2 b1)))

;; heap
(declare-datatypes () ((Execution (cons (head Int) (tail Execution)) (start))))

;; vars and unint functions
(declare-fun nil () Int)
(declare-fun c () Int)

(declare-fun prv_cfg (Int) Int)
(declare-fun nxt (Int) Int)
(declare-fun v1 (Int) Int)
(declare-fun v2 (Int) Int)

;; recdefs
(declare-fun reach_pgm (Execution) Bool)

(define-fun cond ((x Int)) Bool
  (not (= (v1 (prv_cfg x)) nil))
)

(define-fun assign ((x Int)) Bool
  (and (= (v1 x) (nxt (v1 (prv_cfg x))))
       (= (v2 x) (nxt (v2 (prv_cfg x)))))
)

(define-fun body ((x Int)) Bool
  (and (cond x) (assign x))
)

(assert (forall ((x Execution))
                (iff (reach_pgm x)
                     (ite (= x start)
                          true
                          (and (= (prv_cfg (head x)) (head (tail x)))
                               (reach_pgm (tail x))
                               (body (head x)))))))

;; axioms
(assert (= (v1 (head start)) (nxt (v2 (head start)))))

;; goal
(assert (not 
(forall ((x Execution))
        (=> (reach_pgm x)
            (=> (= (v1 (head x)) nil)
                (= (nxt (v2 (head x))) nil))))
))
(check-sat)
