;; preamble
(define-fun iff ((b1 Bool) (b2 Bool)) Bool
  (and (=> b1 b2) (=> b2 b1)))

;; heap
(declare-datatypes () ((DagOfLoc (cons (head Int) (left DagOfLoc) (right DagOfLoc)) (empty))))

;; vars and unint functions
(declare-fun nil () Int)
(declare-fun k () Int)

(declare-fun leftptr (Int) Int)
(declare-fun rightptr (Int) Int)
(declare-fun key (Int) Int)

;; recdefs
(declare-fun dag (DagOfLoc) Bool)
(declare-fun reach (DagOfLoc Int) Bool)

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

(assert (forall ((x DagOfLoc))
                (iff (dag x)
                     (ite (= x empty)
                          true
                          (ite (and (= (leftptr (head x)) nil) (= (rightptr (head x)) nil))
                               (and (= (left x) empty) (= (right x) empty))
                          (ite (and (= (leftptr (head x)) nil) (not (= (rightptr (head x)) nil)))
                               (and (= (left x) empty)
                                    (not (= (right x) empty))
                                    (= (rightptr (head x)) (head (right x)))
                                    (dag (right x)))
                          (ite (and (not (= (leftptr (head x)) nil)) (= (rightptr (head x)) nil))
                               (and (= (right x) empty)
                                    (not (= (left x) empty))
                                    (= (leftptr (head x)) (head (left x)))
                                    (dag (left x)))
                               (and (not (= (right x) empty))
                                    (= (rightptr (head x)) (head (right x)))
                                    (dag (right x))
                                    (not (= (left x) empty))
                                    (= (leftptr (head x)) (head (left x)))
                                    (dag (left x))))))))))

;; goal
(assert (not
(forall ((x DagOfLoc) (y DagOfLoc)) (=> (reach x (head y)) (=> (and (not (= k (key (head x)))) (dag x)) (dag y))))
))
(check-sat)
