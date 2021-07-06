;; preamble
(define-fun iff ((b1 Bool) (b2 Bool)) Bool
  (and (=> b1 b2) (=> b2 b1)))

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; vars and unint functions
(declare-fun nil () Int)
(declare-fun ret () ListOfLoc)

(declare-fun nxt (Int) Int)

;; recdefs
(declare-fun lst (ListOfLoc) Bool)
(declare-fun even_lst (ListOfLoc) Bool)
(declare-fun odd_lst (ListOfLoc) Bool)

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
                (iff (even_lst x)
                     (ite (= x empty)
                          true
                          (ite (= (nxt (head x)) nil)
                               false
                               (and (not (= (tail x) empty))
                                    (= (nxt (head x)) (head (tail x)))
                                    (= (nxt (head (tail x))) (head (tail (tail x))))
                                    (even_lst (tail (tail x)))))))))

(assert (forall ((x ListOfLoc))
                (iff (odd_lst x)
                     (ite (= x empty)
                          false
                          (ite (= (nxt (head x)) nil)
                               (= (tail x) empty)
                               (and (not (= (tail x) empty))
                                    (= (nxt (head x)) (head (tail x)))
                                    (= (nxt (head (tail x))) (head (tail (tail x))))
                                    (odd_lst (tail (tail x)))))))))

;; axioms
(assert (= (nxt nil) nil))

;; goal
(assert (not 
(forall ((x ListOfLoc)) (=> (lst x) (=> (ite (= x empty) (= ret empty) (= ret (tail x)))
                                        (or (even_lst x) (odd_lst x)))))
))
(check-sat)
