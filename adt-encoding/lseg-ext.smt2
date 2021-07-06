;; preamble
(define-fun iff ((b1 Bool) (b2 Bool)) Bool
  (and (=> b1 b2) (=> b2 b1)))

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; vars and unint functions
(declare-fun nil () Int)
(declare-fun k () Int)

(declare-fun nxt (Int) Int)
(declare-fun key (Int) Int)

;; recdefs
(declare-fun lseg (ListOfLoc Int) Bool)

(assert (forall ((x ListOfLoc) (y Int))
                (iff (lseg x y)
                     (ite (= x empty)
                          true
                          (ite (= (nxt (head x)) y)
                               (= (tail x) empty)
                               (and (not (= (tail x) empty))
                                    (= (nxt (head x)) (head (tail x)))
                                    (lseg (tail x) y)))))))

;; goal
(assert (not 
(forall ((x ListOfLoc) (y ListOfLoc) (z ListOfLoc))
        (=> (lseg x (head y))
            (=> (and (not (= k (key (head x)))) (lseg x (head z)))
                 (or (lseg y (head z)) (lseg z (head y))))))
))
(check-sat)
