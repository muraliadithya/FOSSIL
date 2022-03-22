(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((TreeOfLoc (cons (key Int) (left TreeOfLoc) (right TreeOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun leftptr (Int) Int)
(declare-fun rightptr (Int) Int)

;; recdefs
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

(assert (bst empty))
(assert (forall ((k Int) (x ListOfLoc))
        (= (bst (cons k empty empty)) 
           (and (= (leftptr k) nil) (= (leftptr r) nil)))
                (= (hbst k) (
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (dlst (cons k1 (cons k2 x))) 
           (and (= (nxt k1) k2) (= (prv k2) k1) (dlst (cons k2 x))))  
))

(assert (forall ((x TreeOfLoc))
                    (= (minr x)
                       (ite (= x empty) 100 (min3 (key x) (minr (left x)) (minr (right x)))))))

(assert (forall ((x TreeOfLoc))
                    (= (maxr x)
                       (ite (= x empty) (- 1) (max3 (key x) (maxr (left x)) (maxr (right x)))))))

;(assert (not (forall ((x TreeOfLoc)) (< (minr x) (maxr x)))))


(check-sat)
