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
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun lx () TreeOfLoc)
(declare-fun rx () TreeOfLoc)

;; uncommenting both lemmas goes through using cvc4+ig

;; ;; lemma 1
;; (assert (forall ((hx TreeOfLoc) (y Int)) 
;;         (=> (and (bst hx) (member y (hbst hx)))
;;             (<= (key y) (maxr hx)))
;; ))

;; ;; lemma 2
;; (assert (forall ((hx TreeOfLoc) (y Int)) 
;;         (=> (and (bst hx) (member y (hbst hx)))
;;             (<= (minr hx) (key y)))
;; ))

;; goal
(assert (not
        (=> (and (bst hx) (= hx (cons x lx rx)) (not (= x nil))
                 (member y (hbst lx)) (member z (hbst rx)))
	    (<= (key y) (key z)))
))

(check-sat)
