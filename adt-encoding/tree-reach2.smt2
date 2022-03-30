(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((TreeOfLoc (cons (head Int) (left TreeOfLoc) (right TreeOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun leftptr (Int) Int)
(declare-fun rightptr (Int) Int)
(declare-fun key (Int) Int)

;; recdefs
(declare-fun htree (TreeOfLoc) (Set Int))
(declare-fun tree (TreeOfLoc) Bool)
(declare-fun reach (TreeOfLoc Int) Bool)

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

;; reach definition

(assert (forall ((y Int)) (reach empty y)))
(assert (forall ((k Int) (y Int))
        (= (reach (cons k empty empty) y)
           (and (not (= k nil)) (or (= (leftptr k) y) (= (rightptr k) y))))
))
(assert (forall ((k Int) (kl Int) (xl TreeOfLoc) (yl TreeOfLoc) (y Int))
        (= (reach (cons k (cons kl xl yl) empty) y)
           (and (= (leftptr k) kl) (not (= k nil))
                (reach (cons kl xl yl) y)))
))
(assert (forall ((k Int) (kr Int) (xr TreeOfLoc) (yr TreeOfLoc) (y Int))
        (= (reach (cons k empty (cons kr xr yr)) y)
           (and (= (rightptr k) kr) (not (= k nil))
                (reach (cons kr xr yr) y)))
))
(assert (forall ((k Int) (kl Int) (kr Int)
                 (xl TreeOfLoc) (yl TreeOfLoc) (xr TreeOfLoc) (yr TreeOfLoc) (y Int))
        (= (reach (cons k (cons kl xl yl) (cons kr xr yr)) y)
           (and (= (leftptr k) kl) (= (rightptr k) kr) (not (= k nil))
                (or (reach (cons kl xl yl) y) (reach (cons kr xr yr) y))))
))

(assert (forall ((k Int) (kl Int) (xl TreeOfLoc) (yl TreeOfLoc) (y Int))
        (= (reach (cons k (cons kl xl yl) empty) y)
           (and (= (leftptr k) kl) (= (rightptr k) y) (not (= k nil))))
))
(assert (forall ((k Int) (kr Int) (xr TreeOfLoc) (yr TreeOfLoc) (y Int))
        (= (reach (cons k empty (cons kr xr yr)) y)
           (and (= (leftptr k) y) (= (rightptr k) kr) (not (= k nil))))
))

;; axioms
(assert (= (leftptr nil) nil))
(assert (= (rightptr nil) nil))

(declare-fun hx () TreeOfLoc)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun k () Int)
(declare-fun lx () TreeOfLoc)
(declare-fun rx () TreeOfLoc)
(declare-fun lrets () TreeOfLoc)
(declare-fun rrets () TreeOfLoc)

;; uncommenting lemma goes through using cvc4+ig

;; ;; lemma
;; (assert (forall ((hx TreeOfLoc) (y Int) (ly TreeOfLoc) (ry TreeOfLoc) (hy TreeOfLoc))
;;         (=> (and (reach hx y) (= hy (cons y ly ry))) (=> (tree hx) (tree hy)))
;; ))

;; goal
(assert (not
        (=> (and (tree hx) (reach hx y))
            (exists ((hret TreeOfLoc))
                    (and (tree hret) (= hret (cons y lrets rrets)))))
))

(check-sat)
