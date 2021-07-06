;; preamble
(define-fun iff ((b1 Bool) (b2 Bool)) Bool
  (and (=> b1 b2) (=> b2 b1)))

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; vars and unint functions
(declare-fun nil () Int)
(declare-fun ret () ListOfLoc)

(declare-fun nxt (Int) Int)
(declare-fun prv (Int) Int)
(declare-fun key (Int) Int)

;; recdefs
(declare-fun dlst (ListOfLoc) Bool)
(declare-fun slst (ListOfLoc) Bool)
(declare-fun sdlst (ListOfLoc) Bool)

(assert (forall ((x ListOfLoc))
                (iff (dlst x)
                     (ite (= x empty)
                          true
                          (ite (= (nxt (head x)) nil)
                               (= (tail x) empty)
                               (and (not (= (tail x) empty))
                                    (= (nxt (head x)) (head (tail x)))
                                    (= (prv (head (tail x))) (head x))
                                    (dlst (tail x))))))))

(assert (forall ((x ListOfLoc))
                (iff (sdlst x)
                     (ite (= x empty)
                          true
                          (ite (= (nxt (head x)) nil)
                               (= (tail x) empty)
                               (and (not (= (tail x) empty))
                                    (= (nxt (head x)) (head (tail x)))
                                    (= (prv (head (tail x))) (head x))
                                    (<= (key (head x)) (key (nxt (head x))))
                                    (sdlst (tail x))))))))

;; goal
(assert (not 
(forall ((x ListOfLoc)) (=> (sdlst x) (=> (ite (= x empty) (= ret empty) (= ret (tail x))) (dlst ret))))
))
(check-sat)
