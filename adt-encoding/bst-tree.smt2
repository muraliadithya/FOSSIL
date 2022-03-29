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
(declare-fun htree (TreeOfLoc) (Set Int))
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

;; htree definition

(assert (= (htree empty) (as emptyset (Set Int))))
(assert (forall ((k Int) (lt TreeOfLoc) (rt TreeOfLoc))
        (= (htree (cons k lt rt)) (insert k (union (htree lt) (htree rt))))
))

;; binary tree definition

(assert (tree empty))
(assert (forall ((k Int))
        (= (tree (cons k empty empty))
           (and (not (= k nil)) (= (leftptr k) nil) (= (rightptr k) nil)))
))
(assert (forall ((k Int) (kl Int) (xl TreeOfLoc) (yl TreeOfLoc))
        (= (tree (cons k (cons kl xl yl) empty))
           (and (= (leftptr k) kl) (= (rightptr k) nil) (not (= k nil))
                (not (member k (htree (cons kl xl yl))))
                (tree (cons kl xl yl))))
))
(assert (forall ((k Int) (kr Int) (xr TreeOfLoc) (yr TreeOfLoc))
        (= (tree (cons k empty (cons kr xr yr)))
           (and (= (leftptr k) nil) (= (rightptr k) kr) (not (= k nil))
                (not (member k (htree (cons kr xr yr))))
                (tree (cons kr xr yr))))
))
(assert (forall ((k Int) (kl Int) (kr Int) 
                 (xl TreeOfLoc) (yl TreeOfLoc) (xr TreeOfLoc) (yr TreeOfLoc))
        (= (tree (cons k (cons kl xl yl) (cons kr xr yr)))
           (and (= (leftptr k) kl) (= (rightptr k) kr) (not (= k nil))
                (not (member k (htree (cons kl xl yl))))
                (not (member k (htree (cons kr xr yr))))
                (= (intersection (htree (cons kl xl yl)) (htree (cons kr xr yr)))
                   (as emptyset (Set Int)))
                (tree (cons kl xl yl)) (tree (cons kr xr yr))))
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
                (not (member k (htree (cons kl xl yl))))
                (bst (cons kl xl yl))))
))
(assert (forall ((k Int) (kr Int) (xr TreeOfLoc) (yr TreeOfLoc))
        (= (bst (cons k empty (cons kr xr yr)))
           (and (= (leftptr k) nil) (= (rightptr k) kr) (not (= k nil))
                (< 0 (key k)) (< (key k) 100) (<= (key k) (minr (cons kr xr yr)))
                (not (member k (htree (cons kr xr yr))))
                (bst (cons kr xr yr))))
))
(assert (forall ((k Int) (kl Int) (kr Int) 
                 (xl TreeOfLoc) (yl TreeOfLoc) (xr TreeOfLoc) (yr TreeOfLoc))
        (= (bst (cons k (cons kl xl yl) (cons kr xr yr)))
           (and (= (leftptr k) kl) (= (rightptr k) kr) (not (= k nil))
                (< 0 (key k)) (< (key k) 100)
                (<= (maxr (cons kl xl yl)) (key k)) (<= (key k) (minr (cons kr xr yr)))
                (not (member k (htree (cons kl xl yl))))
                (not (member k (htree (cons kr xr yr))))
                (= (intersection (htree (cons kl xl yl)) (htree (cons kr xr yr)))
                   (as emptyset (Set Int)))
                (bst (cons kl xl yl)) (bst (cons kr xr yr))))
))

;; axioms
(assert (= (leftptr nil) nil))
(assert (= (rightptr nil) nil))

(declare-fun hx () TreeOfLoc)
(declare-fun x () Int)
(declare-fun lx () TreeOfLoc)
(declare-fun rx () TreeOfLoc)
(declare-fun ret () Int)
(declare-fun lrets () TreeOfLoc)
(declare-fun rrets () TreeOfLoc)

;; faithful encoding

;; goal
(assert (not
        (=> (and (bst hx) (= hx (cons x lx rx)))
	    (=> (ite (= x nil) (= ret nil) (= ret (leftptr x)))
                (exists ((hret TreeOfLoc))
                        (and (tree hret) (= hret (cons ret lrets rrets))))))
))

;; uncommenting below goes through using cvc4+ig (need lemma assumed)

;; ;; lemma
;; (assert (forall ((hx TreeOfLoc)) (=> (bst hx) (tree hx))))

;; ;; goal with explicit heaplets
;; (assert (not
;;         (=> (and (bst hx) (= hx (cons x lx rx)))
;; 	    (=> (ite (= x nil) (= ret nil) (= ret (leftptr x)))
;;                 (ite (= ret nil) (tree empty)
;;                      (and (tree lx) (= (head lx) ret)))))
;; ))

(check-sat)
