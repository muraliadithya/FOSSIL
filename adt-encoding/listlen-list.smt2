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

;; recdefs
(declare-fun lst (ListOfLoc) Bool)
(declare-fun lstlen_bool (ListOfLoc) Bool)
(declare-fun lstlen_int (ListOfLoc) Int)

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
                (iff (lstlen_bool x)
                     (ite (= x empty)
                          true
                          (ite (= (nxt (head x)) nil)
                               (= (tail x) empty)
                               (and (not (= (tail x) empty))
                                    (= (nxt (head x)) (head (tail x)))
                                    (lstlen_bool (tail x))))))))

(assert (forall ((x ListOfLoc))
                (ite (= x empty)
                     (= (lstlen_int x) 0)
                     (ite (= (nxt (head x)) nil)
                          (and (= (tail x) empty)
                               (= (lstlen_int x) 1))
                          (and (not (= (tail x) empty))
                               (= (nxt (head x)) (head (tail x)))
                               (= (listlen_int x) (+ 1 (lstlen_int (tail x)))))))))

;; axioms
(assert (= (nxt nil) nil))

;; goal
(assert (not 
(forall ((x ListOfLoc)) (=> (lstlen_bool x)
                            (=> (ite (= (lstlen_int x) 1)
                                     (= ret x)
                                     (= ret (tail x)))
                                (lst ret))))
))
(check-sat)
