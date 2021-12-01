;; preamble
(define-fun iff ((b1 Bool) (b2 Bool)) Bool
  (and (=> b1 b2) (=> b2 b1)))

;; heap
(declare-datatypes () ((DagOfLoc (cons (head Int) (left DagOfLoc) (right DagOfLoc)) (empty))))

;; vars and unint functions
(declare-fun nil () Int)
(declare-fun ret () DagOfLoc)
(declare-fun k () Int)

(declare-fun leftptr (Int) Int)
(declare-fun rightptr (Int) Int)
(declare-fun parentptr (Int) Int)
(declare-fun key (Int) Int)

;; recdefs
(declare-fun htree (DagOfLoc) (Set Int))
(declare-fun tree_p (DagOfLoc) Bool)
(declare-fun reach (DagOfLoc Int) Bool)

(assert (forall ((x DagOfLoc))
                (ite (= x empty)
                     (= (htree x) (as emptyset (Set Int)))
                     (ite (and (= (leftptr (head x)) nil) (= (rightptr (head x)) nil))
                          (and (= (left x) empty) (= (right x) empty)
                               (= (htree x) (singleton (head x))))
                     (ite (and (= (leftptr (head x)) nil) (not (= (rightptr (head x)) nil)))
                          (and (= (left x) empty)
                               (not (= (right x) empty))
                               (= (rightptr (head x)) (head (right x)))
                               (= (htree x) (insert (head x) (htree (right x)))))
                     (ite (and (not (= (leftptr (head x)) nil)) (= (rightptr (head x)) nil))
                          (and (= (right x) empty)
                               (not (= (left x) empty))
                               (= (leftptr (head x)) (head (left x)))
                               (= (htree x) (insert (head x) (htree (left x)))))
                          (and (not (= (right x) empty))
                               (= (rightptr (head x)) (head (right x)))
                               (not (= (left x) empty))
                               (= (leftptr (head x)) (head (left x)))
                               (= (htree x) (insert (head x) (union (htree (left x)) (htree (right x))))))))))))

(assert (forall ((x DagOfLoc))
                (iff (tree_p x)
                     (ite (= x empty)
                          true
                          (and (= (intersection (htree (left x)) (htree (right x))) (as emptyset (Set Int)))
                               (ite (= (leftptr (head x)) nil) true
                                    (= (parentptr (leftptr (head x))) (head x)))
                               (ite (= (rightptr (head x)) nil) true
                                    (= (parentptr (rightptr (head x))) (head x)))
                          (ite (and (= (leftptr (head x)) nil) (= (rightptr (head x)) nil))
                               (and (= (left x) empty) (= (right x) empty))
                          (ite (and (= (leftptr (head x)) nil) (not (= (rightptr (head x)) nil)))
                               (and (= (left x) empty)
                                    (not (= (right x) empty))
                                    (= (rightptr (head x)) (head (right x)))
                                    (tree_p (right x)))
                          (ite (and (not (= (leftptr (head x)) nil)) (= (rightptr (head x)) nil))
                               (and (= (right x) empty)
                                    (not (= (left x) empty))
                                    (= (leftptr (head x)) (head (left x)))
                                    (tree_p (left x)))
                               (and (not (= (right x) empty))
                                    (= (rightptr (head x)) (head (right x)))
                                    (tree_p (right x))
                                    (not (= (left x) empty))
                                    (= (leftptr (head x)) (head (left x)))
                                    (tree_p (left x)))))))))))

(assert (forall ((x DagOfLoc) (y Int))
                (iff (reach x y)
                     (ite (= x empty)
                          true
                          (ite (= (leftptr (head x)) y)
                               (= (left x) empty)
                               (ite (= (rightptr (head x)) y)
                                    (= (right x) empty)
                                    (and (not (= (left x) empty))
                                         (not (= (right x) empty))
                                         (= (leftptr (head x)) (head (left x)))
                                         (= (rightptr (head x)) (head (right x)))
                                         (or (reach (left x) y)
                                             (reach (right x) y)))))))))

;; goal
(assert (not
(forall ((x DagOfLoc) (y DagOfLoc))
        (=> (tree_p x)
            (=> (reach x (head y))
                (tree_p y))))
))
(check-sat)
