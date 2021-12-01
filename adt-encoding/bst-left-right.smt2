(declare-datatypes () ((TreeOfLoc (cons (key Int) (left TreeOfLoc) (right TreeOfLoc)) (empty))))

(declare-fun nil () Int)

(declare-fun leftptr (Int) Int)
(declare-fun rightptr (Int) Int)

(declare-fun bst (TreeOfLoc) Bool)
(declare-fun hbst (TreeOfLoc) (Set Int))
(declare-fun minr (TreeOfLoc) Int)
(declare-fun maxr (TreeOfLoc) Int)

(define-fun iff ((b1 Bool) (b2 Bool)) Bool
    (and (=> b1 b2) (=> b2 b1)))
(define-fun min3 ((a Int) (b Int) (c Int)) Int
    (ite (< a b) (ite (< a c) a c) (ite (< b c) b c)))
(define-fun max3 ((a Int) (b Int) (c Int)) Int
    (ite (> a b) (ite (> a c) a c) (ite (> b c) b c)))

(assert (forall ((x TreeOfLoc))
                    (= (minr x)
                       (ite (= x empty) 100 (min3 (key x) (minr (left x)) (minr (right x)))))))

(assert (forall ((x TreeOfLoc))
                    (= (maxr x)
                       (ite (= x empty) (- 1) (max3 (key x) (maxr (left x)) (maxr (right x)))))))

;(assert (not (forall ((x TreeOfLoc)) (< (minr x) (maxr x)))))


(check-sat)
