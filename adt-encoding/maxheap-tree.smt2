(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((DagOfLoc (cons (head Int) (left DagOfLoc) (right DagOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun leftptr (Int) Int)
(declare-fun rightptr (Int) Int)
(declare-fun key (Int) Int)

;; recdefs
(declare-fun tree (DagOfLoc) Bool)
(declare-fun htree (DagOfLoc) (Set Int))
(declare-fun maxheap (DagOfLoc) Bool)

;; htree definition

(assert (= (htree empty) (as emptyset (Set Int))))
(assert (forall ((k Int) (lt DagOfLoc) (rt DagOfLoc))
        (= (htree (cons k lt rt)) (insert k (union (htree lt) (htree rt))))
))

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

;; max heap definition

(assert (maxheap empty))
(assert (forall ((k Int))
        (= (maxheap (cons k empty empty))
           (and (not (= k nil)) (= (leftptr k) nil) (= (rightptr k) nil)))
))
(assert (forall ((k Int) (kl Int) (xl DagOfLoc) (yl DagOfLoc))
        (= (maxheap (cons k (cons kl xl yl) empty))
           (and (= (leftptr k) kl) (= (rightptr k) nil) (not (= k nil))
                (<= (key kl) (key k))
                (not (member k (htree (cons kl xl yl))))
                (maxheap (cons kl xl yl))))
))
(assert (forall ((k Int) (kr Int) (xr DagOfLoc) (yr DagOfLoc))
        (= (maxheap (cons k empty (cons kr xr yr)))
           (and (= (leftptr k) nil) (= (rightptr k) kr) (not (= k nil))
                (<= (key k) (key kr))
                (not (member k (htree (cons kr xr yr))))
                (maxheap (cons kr xr yr))))
))
(assert (forall ((k Int) (kl Int) (kr Int) 
                 (xl DagOfLoc) (yl DagOfLoc) (xr DagOfLoc) (yr DagOfLoc))
        (= (maxheap (cons k (cons kl xl yl) (cons kr xr yr)))
           (and (= (leftptr k) kl) (= (rightptr k) kr) (not (= k nil))
                (<= (key kl) (key k)) (<= (key k) (key kr))
                (not (member k (htree (cons kl xl yl))))
                (not (member k (htree (cons kr xr yr))))
                (= (intersection (htree (cons kl xl yl)) (htree (cons kr xr yr)))
                   (as emptyset (Set Int)))
                (maxheap (cons kl xl yl)) (maxheap (cons kr xr yr))))
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
        (=> (and (maxheap hx) (= hx (cons x lx rx)))
	    (=> (ite (= x nil) (= ret nil) (= ret (leftptr x)))
                (exists ((hret DagOfLoc))
                        (and (tree hret) (= hret (cons ret lrets rrets))))))
))

;; uncommenting below goes through using cvc4+ig (need lemma assumed)

;; ;; lemma
;; (assert (forall ((hx DagOfLoc)) (=> (maxheap hx) (tree hx))))

;; ;; goal with explicit heaplets
;; (assert (not
;;         (=> (and (maxheap hx) (= hx (cons x lx rx)))
;; 	    (=> (ite (= x nil) (= ret nil) (= ret (leftptr x)))
;;                 (ite (= ret nil) (tree empty)
;;                      (and (tree lx) (= (head lx) ret)))))
;; ))

(check-sat)
