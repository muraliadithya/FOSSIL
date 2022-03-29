(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((DagOfLoc (cons (head Int) (left DagOfLoc) (right DagOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun leftptr (Int) Int)
(declare-fun rightptr (Int) Int)
(declare-fun key (Int) Int)

;; recdefs
(declare-fun dag (DagOfLoc) Bool)
(declare-fun reach (DagOfLoc Int) Bool)

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

;; reach definition

(assert (forall ((y Int)) (reach empty y)))
(assert (forall ((k Int) (y Int))
        (= (reach (cons k empty empty) y)
           (and (not (= k nil)) (or (= (leftptr k) y) (= (rightptr k) y))))
))
(assert (forall ((k Int) (kl Int) (xl DagOfLoc) (yl DagOfLoc) (y Int))
        (= (reach (cons k (cons kl xl yl) empty) y)
           (and (= (leftptr k) kl) (not (= k nil))
                (reach (cons kl xl yl) y)))
))
(assert (forall ((k Int) (kr Int) (xr DagOfLoc) (yr DagOfLoc) (y Int))
        (= (reach (cons k empty (cons kr xr yr)) y)
           (and (= (rightptr k) kr) (not (= k nil))
                (reach (cons kr xr yr) y)))
))
(assert (forall ((k Int) (kl Int) (kr Int)
                 (xl DagOfLoc) (yl DagOfLoc) (xr DagOfLoc) (yr DagOfLoc) (y Int))
        (= (reach (cons k (cons kl xl yl) (cons kr xr yr)) y)
           (and (= (leftptr k) kl) (= (rightptr k) kr) (not (= k nil))
                (or (reach (cons kl xl yl) y) (reach (cons kr xr yr) y))))
))

(assert (forall ((k Int) (kl Int) (xl DagOfLoc) (yl DagOfLoc) (y Int))
        (= (reach (cons k (cons kl xl yl) empty) y)
           (and (= (leftptr k) kl) (= (rightptr k) y) (not (= k nil))))
))
(assert (forall ((k Int) (kr Int) (xr DagOfLoc) (yr DagOfLoc) (y Int))
        (= (reach (cons k empty (cons kr xr yr)) y)
           (and (= (leftptr k) y) (= (rightptr k) kr) (not (= k nil))))
))

;; axioms
(assert (= (leftptr nil) nil))
(assert (= (rightptr nil) nil))

(declare-fun hx () DagOfLoc)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun k () Int)
(declare-fun lx () DagOfLoc)
(declare-fun rx () DagOfLoc)
(declare-fun lrets () DagOfLoc)
(declare-fun rrets () DagOfLoc)

;; uncommenting lemma goes through using cvc4+ig

;; ;; lemma
;; (assert (forall ((hx DagOfLoc) (y Int) (ly DagOfLoc) (ry DagOfLoc) (hy DagOfLoc))
;;         (=> (and (reach hx y) (= hy (cons y ly ry))) (=> (dag hx) (dag hy)))
;; ))

;; goal
(assert (not
        (=> (and (reach hx y) (= hx (cons x lx rx)) (not (= (key x) k)) (dag hx))
            (exists ((hret DagOfLoc))
                    (and (dag hret) (= hret (cons y lrets rrets)))))
))

(check-sat)
