;; preamble
(define-fun iff ((b1 Bool) (b2 Bool)) Bool
  (and (=> b1 b2) (=> b2 b1)))

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; vars and unint functions
(declare-fun nil () Int)
(declare-fun ret () ListOfLoc)

(declare-fun nxt (Int) Int)
(declare-fun key (Int) Int) ;; TODO: is this ok

;; recdefs
(declare-fun slst (ListOfLoc) Bool)
(declare-fun slseg (ListOfLoc Int) Bool)

(assert (forall ((x ListOfLoc))
                (iff (slst x)
                     (ite (= x empty)
                          true
                          (ite (= (nxt (head x)) nil)
                               (= (tail x) empty)
                               (and (not (= (tail x) empty))
                                    (= (nxt (head x)) (head (tail x)))
                                    (<= (key (head x)) (key (nxt (head x))))
                                    (slst (tail x))))))))

(assert (forall ((x ListOfLoc) (y Int))
                (iff (slseg x y)
                     (ite (= x empty)
                          true
                          (ite (= (nxt (head x)) y)
                               (= (tail x) empty)
                               (and (not (= (tail x) empty))
                                    (= (nxt (head x)) (head (tail x)))
                                    (<= (key (head x)) (key (nxt (head x))))
                                    (slseg (tail x) y)))))))

;; goal
(assert (not 
(forall ((x ListOfLoc) (y ListOfLoc))
        (=> (slseg x (head y)) (=> (= (head y) nil)
                                   (=> (ite (= x empty) (= ret empty) (= ret (tail x)))
                                       (slst ret)))))
))
(check-sat)
