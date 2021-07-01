;; preamble
(define-fun iff ((b1 Bool) (b2 Bool)) Bool
  (and (=> b1 b2) (=> b2 b1)))

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; vars and unint functions
(declare-fun nil () Int)

(declare-fun nxt (Int) Int)
(declare-fun prv (Int) Int)

;; recdefs
(declare-fun lseg (ListOfLoc Int) Bool)
(declare-fun cyclic (ListOfLoc) Bool)

(assert (forall ((x ListOfLoc) (y Int))
                (iff (lseg x y)
                     (ite (= x empty)
                          true
                          (ite (= (nxt (head x)) y)
                               (= (tail x) empty)
                               (and (not (= (tail x) empty))
                                    (= (nxt (head x)) (head (tail x)))
                                    (lseg (tail x) y)))))))

(assert (forall ((x ListOfLoc)) (= (cyclic x) (lseg (tail x) (head x)))))

;; goal
(assert (not
(forall ((x ListOfLoc)) (=> (cyclic x) (cyclic (tail x))))
))
(check-sat)
