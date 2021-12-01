;; preamble
(define-fun iff ((b1 Bool) (b2 Bool)) Bool
  (and (=> b1 b2) (=> b2 b1)))

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; vars and unint functions
(declare-fun nil () Int)
(declare-fun ret () ListOfLoc)

(declare-fun nxt (Int) Int)
(declare-fun red (Int) Bool)
(declare-fun black (Int) Bool)

;; recdefs
(declare-fun lst (ListOfLoc) Bool)
(declare-fun rlst (ListOfLoc) Bool)

(assert (forall ((x ListOfLoc))
                (iff (lst x)
                     (ite (= x empty)
                          true
                          (ite (= (nxt (head x)) nil)
                               (= (tail x) empty)
                               (and (not (= (tail x) empty))
                                    (= (nxt (head x)) (head (tail x)))
                                    (lst (tail x))))))))

(assert (forall ((x ListOfLoc))
                (iff (rlst x)
                     (ite (= x empty)
                          true
                          (ite (= (nxt (head x)) nil)
                               (= (tail x) empty)
                               (and (not (= (tail x) empty))
                                    (= (nxt (head x)) (head (tail x)))
                                    (or (and (red (head x)) (not (black (head x)))
                                             (black (nxt (head x))) (not (red (nxt (head x)))))
                                        (and (black (head x)) (not (red (head x)))
                                             (red (nxt (head x))) (not (black (nxt (head x))))))
                                    (rlst (tail x))))))))

;; axioms
(assert (= (nxt nil) nil))
(assert (red nil))

;; goal
(assert (not 
(forall ((x ListOfLoc)) (=> (rlst x) (=> (ite (= x empty) (= ret empty) (= ret (tail x))) (lst ret))))
))
(check-sat)
