(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((DagOfLoc (cons (head Int) (left DagOfLoc) (right DagOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun leftptr (Int) Int)
(declare-fun rightptr (Int) Int)

;; recdefs
(declare-fun htree (DagOfLoc) (Set Int))
(declare-fun tree (DagOfLoc) Bool)
(declare-fun dag (DagOfLoc) Bool)

;; dag definition

(assert (dag empty))
(assert (forall ((k Int))
        (= (dag (cons k empty empty))
           (and (not (= k nil)) (= (leftptr k) nil) (= (rightptr k) nil)))
))
(assert (forall ((k Int) (kl Int) (xl DagOfLoc) (yl DagOfLoc))
        (= (dag (cons k (cons kl xl yl) empty))
           (and (= (leftptr k) kl) (= (rightptr k) nil) (not (= k nil))
                (dag (cons kl xl yl))))
))
(assert (forall ((k Int) (kr Int) (xr DagOfLoc) (yr DagOfLoc))
        (= (dag (cons k empty (cons kr xr yr)))
           (and (= (leftptr k) nil) (= (rightptr k) kr) (not (= k nil))
                (dag (cons kr xr yr))))
))
(assert (forall ((k Int) (kl Int) (kr Int) 
                 (xl DagOfLoc) (yl DagOfLoc) (xr DagOfLoc) (yr DagOfLoc))
        (= (dag (cons k (cons kl xl yl) (cons kr xr yr)))
           (and (= (leftptr k) kl) (= (rightptr k) kr) (not (= k nil))
                (dag (cons kl xl yl)) (dag (cons kr xr yr))))
))

;; htree definition

(assert (= (htree empty) (as emptyset (Set Int))))
(assert (forall ((k Int) (lt DagOfLoc) (rt DagOfLoc))
        (= (htree (cons k lt rt)) (insert k (union (htree lt) (htree rt))))
))

;; binary tree definition

(assert (tree empty))
(assert (forall ((k Int))
        (= (tree (cons k empty empty))
           (and (not (= k nil)) (= (leftptr k) nil) (= (rightptr k) nil)))
))
(assert (forall ((k Int) (kl Int) (xl DagOfLoc) (yl DagOfLoc))
        (= (tree (cons k (cons kl xl yl) empty))
           (and (= (leftptr k) kl) (= (rightptr k) nil) (not (= k nil))
                (not (member k (htree (cons kl xl yl))))
                (tree (cons kl xl yl))))
))
(assert (forall ((k Int) (kr Int) (xr DagOfLoc) (yr DagOfLoc))
        (= (tree (cons k empty (cons kr xr yr)))
           (and (= (leftptr k) nil) (= (rightptr k) kr) (not (= k nil))
                (not (member k (htree (cons kr xr yr))))
                (tree (cons kr xr yr))))
))
(assert (forall ((k Int) (kl Int) (kr Int) 
                 (xl DagOfLoc) (yl DagOfLoc) (xr DagOfLoc) (yr DagOfLoc))
        (= (tree (cons k (cons kl xl yl) (cons kr xr yr)))
           (and (= (leftptr k) kl) (= (rightptr k) kr) (not (= k nil))
                (not (member k (htree (cons kl xl yl))))
                (not (member k (htree (cons kr xr yr))))
                (= (intersection (htree (cons kl xl yl)) (htree (cons kr xr yr)))
                   (as emptyset (Set Int)))
                (tree (cons kl xl yl)) (tree (cons kr xr yr))))
))

;; axioms
(assert (= (leftptr nil) nil))
(assert (= (rightptr nil) nil))

(declare-fun hx () DagOfLoc)
(declare-fun x () Int)
(declare-fun lx () DagOfLoc)
(declare-fun rx () DagOfLoc)
(declare-fun ret () Int)
(declare-fun lrets () DagOfLoc)
(declare-fun rrets () DagOfLoc)

;; faithful encoding

;; goal
(assert (not
        (=> (and (tree hx) (= hx (cons x lx rx)))
	    (=> (ite (= x nil) (= ret nil) (= ret (leftptr x)))
                (exists ((hret DagOfLoc))
                        (and (dag hret) (= hret (cons ret lrets rrets))))))
))

;; uncommenting below goes through using cvc4+ig (need lemma assumed)

;; ;; lemma
;; (assert (forall ((hx DagOfLoc)) (=> (tree hx) (dag hx))))

;; ;; goal with explicit heaplets
;; (assert (not
;;         (=> (and (tree hx) (= hx (cons x lx rx)))
;; 	    (=> (ite (= x nil) (= ret nil) (= ret (leftptr x)))
;;                 (ite (= ret nil) (tree empty)
;;                      (and (dag lx) (= (head lx) ret)))))
;; ))

(check-sat)
