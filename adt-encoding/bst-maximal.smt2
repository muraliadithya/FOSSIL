(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((TreeOfLoc (cons (head Int) (left TreeOfLoc) (right TreeOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun leftptr (Int) Int)
(declare-fun rightptr (Int) Int)
(declare-fun key (Int) Int)

;; recdefs
(declare-fun minr (TreeOfLoc) Int)
(declare-fun maxr (TreeOfLoc) Int)
(declare-fun hbst (TreeOfLoc) (Set Int))
(declare-fun keys (TreeOfLoc) (Set Int))
(declare-fun tree (TreeOfLoc) Bool)
(declare-fun bst (TreeOfLoc) Bool)

(define-fun min3 ((a Int) (b Int) (c Int)) Int
    (ite (< a b) (ite (< a c) a c) (ite (< b c) b c)))
(define-fun max3 ((a Int) (b Int) (c Int)) Int
    (ite (> a b) (ite (> a c) a c) (ite (> b c) b c)))

;; minr and maxr definitions

(assert (= (minr empty) 100))
(assert (forall ((k Int) (lt TreeOfLoc) (rt TreeOfLoc))
        (= (minr (cons k lt rt)) (min3 (key k) (minr lt) (minr rt)))
))

(assert (= (maxr empty) (- 1)))
(assert (forall ((k Int) (lt TreeOfLoc) (rt TreeOfLoc))
        (= (maxr (cons k lt rt)) (max3 (key k) (minr lt) (minr rt)))
))

;; hbst definition

(assert (= (hbst empty) (as emptyset (Set Int))))
(assert (forall ((k Int) (lt TreeOfLoc) (rt TreeOfLoc))
        (= (hbst (cons k lt rt)) (insert k (union (hbst lt) (hbst rt))))
))

;; keys definition

(assert (= (keys empty) (as emptyset (Set Int))))
(assert (forall ((k Int) (lt TreeOfLoc) (rt TreeOfLoc))
        (= (keys (cons k lt rt)) (insert (key k) (union (keys lt) (keys rt))))
))

;; bst definition

(assert (bst empty))
(assert (forall ((k Int))
        (= (bst (cons k empty empty))
           (and (not (= k nil)) (= (leftptr k) nil) (= (rightptr k) nil)
                (< 0 (key k)) (< (key k) 100)))
))
(assert (forall ((k Int) (kl Int) (xl TreeOfLoc) (yl TreeOfLoc))
        (= (bst (cons k (cons kl xl yl) empty))
           (and (= (leftptr k) kl) (= (rightptr k) nil) (not (= k nil))
                (< 0 (key k)) (< (key k) 100) (<= (maxr (cons kl xl yl)) (key k))
                (not (member k (hbst (cons kl xl yl))))
                (bst (cons kl xl yl))))
))
(assert (forall ((k Int) (kr Int) (xr TreeOfLoc) (yr TreeOfLoc))
        (= (bst (cons k empty (cons kr xr yr)))
           (and (= (leftptr k) nil) (= (rightptr k) kr) (not (= k nil))
                (< 0 (key k)) (< (key k) 100) (<= (key k) (minr (cons kr xr yr)))
                (not (member k (hbst (cons kr xr yr))))
                (bst (cons kr xr yr))))
))
(assert (forall ((k Int) (kl Int) (kr Int) 
                 (xl TreeOfLoc) (yl TreeOfLoc) (xr TreeOfLoc) (yr TreeOfLoc))
        (= (bst (cons k (cons kl xl yl) (cons kr xr yr)))
           (and (= (leftptr k) kl) (= (rightptr k) kr) (not (= k nil))
                (< 0 (key k)) (< (key k) 100)
                (<= (maxr (cons kl xl yl)) (key k)) (<= (key k) (minr (cons kr xr yr)))
                (not (member k (hbst (cons kl xl yl))))
                (not (member k (hbst (cons kr xr yr))))
                (= (intersection (hbst (cons kl xl yl)) (hbst (cons kr xr yr)))
                   (as emptyset (Set Int)))
                (bst (cons kl xl yl)) (bst (cons kr xr yr))))
))

;; axioms
(assert (= (leftptr nil) nil))
(assert (= (rightptr nil) nil))

(declare-fun hx () TreeOfLoc)
(declare-fun x1 () Int)
(declare-fun lx1 () TreeOfLoc)
(declare-fun rx1 () TreeOfLoc)
(declare-fun x2 () Int)
(declare-fun lx2 () TreeOfLoc)
(declare-fun rx2 () TreeOfLoc)
(declare-fun hy () TreeOfLoc)
(declare-fun y () Int)
(declare-fun ly () TreeOfLoc)
(declare-fun ry () TreeOfLoc)
(declare-fun k () Int)
(declare-fun lrets () TreeOfLoc)
(declare-fun rrets () TreeOfLoc)

;; uncommenting lemma goes through using cvc4+ig

;; ;; lemma
;; (assert (forall ((hx TreeOfLoc) (hy TreeOfLoc) (y Int) (ly TreeOfLoc) (ry TreeOfLoc))
;;         (=> (and (bst hx) (= hy (cons y ly ry)) (member y (hbst hx)))
;;             (bst hy))
;; ))

;; goal
(assert (not
        (=> (and (bst hx) (= hx (cons x1 lx1 rx1)) (not (= x1 nil))
                 (= rx1 (cons x2 lx2 rx2)) (not (= x2 nil))
                 (= hy (cons y ly ry))
                 (not (= y nil))
                 (member y (hbst hx))
                 (= k (maxr hx))
                 (= k (maxr hy)))
             (exists ((hret TreeOfLoc))
                     (and (= (maxr hret) k) (= hret (cons x2 lrets rrets)))))
))

(check-sat)
