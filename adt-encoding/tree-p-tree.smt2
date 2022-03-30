(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((TreeOfLoc (cons (head Int) (left TreeOfLoc) (right TreeOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun leftptr (Int) Int)
(declare-fun rightptr (Int) Int)
(declare-fun parentptr (Int) Int)

;; recdefs
(declare-fun htree (TreeOfLoc) (Set Int))
(declare-fun tree (TreeOfLoc) Bool)
(declare-fun tree_p (TreeOfLoc) Bool)

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

;; binary tree with additional parent pointer

(assert (tree_p empty))
(assert (forall ((k Int))
        (= (tree_p (cons k empty empty))
           (and (not (= k nil)) (= (leftptr k) nil) (= (rightptr k) nil)))
))
(assert (forall ((k Int) (kl Int) (xl TreeOfLoc) (yl TreeOfLoc))
        (= (tree_p (cons k (cons kl xl yl) empty))
           (and (= (leftptr k) kl) (= (rightptr k) nil) (= (parentptr kl) k) (not (= k nil))
                (not (member k (htree (cons kl xl yl))))
                (tree_p (cons kl xl yl))))
))
(assert (forall ((k Int) (kr Int) (xr TreeOfLoc) (yr TreeOfLoc))
        (= (tree_p (cons k empty (cons kr xr yr)))
           (and (= (leftptr k) nil) (= (rightptr k) kr) (= (parentptr kr) k) (not (= k nil))
                (not (member k (htree (cons kr xr yr))))
                (tree_p (cons kr xr yr))))
))
(assert (forall ((k Int) (kl Int) (kr Int) 
                 (xl TreeOfLoc) (yl TreeOfLoc) (xr TreeOfLoc) (yr TreeOfLoc))
        (= (tree_p (cons k (cons kl xl yl) (cons kr xr yr)))
           (and (= (leftptr k) kl) (= (rightptr k) kr) 
                (= (parentptr kl) k) (= (parentptr kr) k) (not (= k nil))
                (not (member k (htree (cons kl xl yl))))
                (not (member k (htree (cons kr xr yr))))
                (= (intersection (htree (cons kl xl yl)) (htree (cons kr xr yr)))
                   (as emptyset (Set Int)))
                (tree_p (cons kl xl yl)) (tree_p (cons kr xr yr))))
))

;; axioms
(assert (= (leftptr nil) nil))
(assert (= (rightptr nil) nil))

(declare-fun hx () TreeOfLoc)
(declare-fun x () Int)
(declare-fun lx () TreeOfLoc)
(declare-fun rx () TreeOfLoc)
(declare-fun lrets () TreeOfLoc)
(declare-fun rrets () TreeOfLoc)

;; faithful encoding

;; goal
(assert (not
        (=> (and (tree_p hx) (= hx (cons x lx rx)) (= (parentptr x) nil))
            (exists ((hret TreeOfLoc))
                    (and (tree hret) (= hret (cons x lrets rrets)))))
))

;; uncommenting below goes through using cvc4+ig (need lemma assumed)

;; ;; lemma
;; (assert (forall ((hx TreeOfLoc)) (=> (tree_p hx) (tree hx))))

;; ;; goal with explicit heaplets
;; (assert (not
;;         (=> (and (tree_p hx) (= hx (cons x lx rx)) (= (parentptr x) nil))
;;             (ite (= x nil) (tree_p empty) (tree_p hx)))
;; ))

(check-sat)
