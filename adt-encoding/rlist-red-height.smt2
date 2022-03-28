(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun nxt (Int) Int)
(declare-fun red (Int) Bool)
(declare-fun black (Int) Bool)

;; recdefs
(declare-fun lst (ListOfLoc) Bool)
(declare-fun rlst (ListOfLoc) Bool)
(declare-fun red_height (ListOfLoc) Int)
(declare-fun black_height (ListOfLoc) Int)

(assert (lst empty))
(assert (forall ((k Int))
        (= (lst (cons k empty))
           (and (not (= k nil)) (= (nxt k) nil)))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (lst (cons k1 (cons k2 x)))
           (and (= (nxt k1) k2) (not (= k1 nil)) (lst (cons k2 x))))
))

(assert (rlst empty))
(assert (forall ((k Int))
        (= (rlst (cons k empty))
           (and (not (= k nil)) (= (nxt k) nil) (black k)))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (rlst (cons k1 (cons k2 x)))
           (and (= (nxt k1) k2) (not (= k1 nil)) (rlst (cons k2 x))
                (or (and (red k1) (not (black k1)) (black k2) (not (red k2)))
                    (and (black k1) (not (red k1)) (red k2) (not (black k2))))))
))

(assert (= (red_height empty) 1))
(assert (forall ((k Int))
        (=> (and (not (= k nil)) (= (nxt k) nil) (red k))
            (= (red_height (cons k empty)) 2))
))
(assert (forall ((k Int))
        (=> (and (not (= k nil)) (= (nxt k) nil) (not (red k)))
            (= (red_height (cons k empty)) 1))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (=> (and (= (nxt k1) k2) (not (= k1 nil)) (red k1))
            (= (red_height (cons k1 (cons k2 x))) (+ 1 (red_height (cons k2 x)))))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (=> (and (= (nxt k1) k2) (not (= k1 nil)) (not (red k1)))
            (= (red_height (cons k1 (cons k2 x))) (red_height (cons k2 x))))
))

(assert (= (black_height empty) 0))
(assert (forall ((k Int))
        (=> (and (not (= k nil)) (= (nxt k) nil) (black k))
            (= (black_height (cons k empty)) 1))
))
(assert (forall ((k Int))
        (=> (and (not (= k nil)) (= (nxt k) nil) (not (black k)))
            (= (black_height (cons k empty)) 0))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (=> (and (= (nxt k1) k2) (not (= k1 nil)) (black k1))
            (= (black_height (cons k1 (cons k2 x))) (+ 1 (black_height (cons k2 x)))))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (=> (and (= (nxt k1) k2) (not (= k1 nil)) (not (black k1)))
            (= (black_height (cons k1 (cons k2 x))) (black_height (cons k2 x))))
))

;; axioms
(assert (= (nxt nil) nil))
(assert (red nil))
(assert (not (black nil)))

(declare-fun hx () ListOfLoc)
(declare-fun x () Int)
(declare-fun xs () ListOfLoc)
(declare-fun ret () Int)
(declare-fun rets () ListOfLoc)

;; uncommenting lemma goes through using cvc4+ig

;; ;; lemma
;; (assert (forall ((hx ListOfLoc)) 
;;                 (=> (and (rlst hx) (= hx (cons x xs)))
;;                     (and (=> (black x) (= (red_height hx) (black_height hx)))
;;                          (=> (red x) (= (red_height hx) (+ 1 (black_height hx))))))
;; ))

;; goal
(assert (not
        (=> (and (rlst hx) (= hx (cons x xs)) (red x))
            (exists ((hret ListOfLoc) (hrets ListOfLoc))
                    (and (= (red_height hret) (+ 1 (black_height hret))) 
                         (= hret (cons x hrets)))))
))

(check-sat)
