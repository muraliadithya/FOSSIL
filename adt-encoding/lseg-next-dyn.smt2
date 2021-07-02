;; preamble
(define-fun iff ((b1 Bool) (b2 Bool)) Bool
  (and (=> b1 b2) (=> b2 b1)))

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; vars and unint functions
(declare-fun nil () Int)
(declare-fun yc () ListOfLoc)
(declare-fun zc () ListOfLoc)
(declare-fun k () Int)

(declare-fun nxt (Int) Int)
(declare-fun key (ListOfLoc) Int)

;; recdefs
(declare-fun lsegy (ListOfLoc) Bool)
(declare-fun lsegz (ListOfLoc) Bool)
(declare-fun lsegy_p (ListOfLoc) Bool)
(declare-fun lsegz_p (ListOfLoc) Bool)

(assert (forall ((x ListOfLoc))
                (iff (lsegy x)
                     (ite (= x empty)
                          true
                          (ite (= (nxt (head x)) (head yc))
                               (= (tail x) empty)
                               (and (not (= (tail x) empty))
                                    (= (nxt (head x)) (head (tail x)))
                                    (lsegy (tail x))))))))

(assert (forall ((x ListOfLoc))
                (iff (lsegz x)
                     (ite (= x empty)
                          true
                          (ite (= (nxt (head x)) (head zc))
                               (= (tail x) empty)
                               (and (not (= (tail x) empty))
                                    (= (nxt (head x)) (head (tail x)))
                                    (lsegz (tail x))))))))

;; TODO: are these correct? next' is only used in recursive call

(assert (forall ((x ListOfLoc))
                (iff (lsegy_p x)
                     (ite (= x empty)
                          true
                          (ite (= (nxt (head x)) (head yc))
                               (= (tail x) empty)
                               (and (not (= (tail x) empty))
                                    (= (nxt (head x)) (head (tail x)))
                                    (ite (= x yc)
                                         (lsegy_p zc)
                                         (lsegy_p (tail x)))))))))

(assert (forall ((x ListOfLoc))
                (iff (lsegz_p x)
                     (ite (= x empty)
                          true
                          (ite (= (nxt (head x)) (head zc))
                               (= (tail x) empty)
                               (and (not (= (tail x) empty))
                                    (= (nxt (head x)) (head (tail x)))
                                    (ite (= x yc)
                                         (lsegz_p zc)
                                         (lsegz_p (tail x)))))))))

;; goal
(assert (not
(forall ((x ListOfLoc)) (=> (lsegy x) (=> (not (= k (key x))) (lsegz_p x))))
))
(check-sat)
