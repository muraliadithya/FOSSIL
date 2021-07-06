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
(declare-fun lst (ListOfLoc) Bool)
(declare-fun lseg (ListOfLoc Int) Bool)
(declare-fun keys (ListOfLoc) (Set Int))

(assert (forall ((x ListOfLoc))
                (iff (lst x)
                     (ite (= x empty)
                          true
                          (ite (= (nxt (head x)) nil)
                               (= (tail x) empty)
                               (and (not (= (tail x) empty))
                                    (= (nxt (head x)) (head (tail x)))
                                    (lst (tail x))))))))

(assert (forall ((x ListOfLoc) (y Int))
                (iff (lseg x y)
                     (ite (= x empty)
                          true
                          (ite (= (nxt (head x)) y)
                               (= (tail x) empty)
                               (and (not (= (tail x) empty))
                                    (= (nxt (head x)) (head (tail x)))
                                    (lseg (tail x) y)))))))

(assert (forall ((x ListOfLoc))
                (ite (= x empty)
                     (= (keys x) (as emptyset (Set Int)))
                     (ite (= (nxt (head x)) nil)
                          (and (= (tail x) empty)
                               (= (keys x) (singleton (key (head x)))))
                          (and (not (= (tail x) empty))
                               (= (nxt (head x)) (head (tail x)))
                               (= (keys x) (insert (key (head x)) (keys (tail x)))))))))

;; axioms
(assert (= (nxt nil) nil))

;; goal
(assert (not 
(forall ((x ListOfLoc) (y ListOfLoc))
        (=> (lseg x (head y))
            (=> (and (not (= x empty)) (not (= y empty)) (lst x) (= (key (head y)) k))
                (member k (keys x)))))
))
(check-sat)
