(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; vars and unint functions
(declare-fun nil () Int)
(declare-fun nxt (Int) Int)
(declare-fun prv (Int) Int)
(declare-fun key (Int) Int)

;; recdefs
(declare-fun dlst (ListOfLoc) Bool)
(declare-fun slst (ListOfLoc) Bool)
(declare-fun sdlst (ListOfLoc) Bool)

(assert (dlst empty))
(assert (forall ((k Int))
        (= (dlst (cons k empty)) 
           (and (not (= k nil)) (= (nxt k) nil)))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (dlst (cons k1 (cons k2 x)))
           (and (= (nxt k1) k2) (not (= k1 nil)) (= (prv k2) k1) (dlst (cons k2 x))))  
))

(assert (slst empty))
(assert (forall ((k Int))
	(= (slst (cons k empty)) (= (nxt k) nil))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc)) 
	(= (slst (cons k1 (cons k2 x))) 
	   (and (= (nxt k1) k2) (not (= k1 nil)) (<= (key k1) (key k2)) (slst (cons k2 x))))
))

(assert (sdlst empty))
(assert (forall ((k Int))
        (= (sdlst (cons k empty)) 
           (and (not (= k nil)) (= (nxt k) nil)))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc))
        (= (sdlst (cons k1 (cons k2 x)))
           (and (= (nxt k1) k2) (not (= k1 nil)) 
                (= (prv k2) k1) (<= (key k1) (key k2)) (sdlst (cons k2 x))))  
))

(declare-fun hx () ListOfLoc)
(declare-fun x () Int)
(declare-fun xs () ListOfLoc)
(declare-fun ret () Int)
(declare-fun rets () ListOfLoc)

;; faithful encoding

;; goal
(assert (not
        (=> (and (sdlst hx) (= hx (cons x xs)))
	    (=> (ite (= x nil) (= ret nil) (= ret (nxt x)))
                (exists ((hret ListOfLoc))
                        (and (dlst hret) (slst hret) (= hret (cons ret rets))))))
))

;; uncommenting below goes through using cvc4+ig (need lemma assumed)

;; ;; lemma
;; (assert (forall ((hx ListOfLoc)) (=> (sdlst hx) (and (dlst hx) (slst hx)))))

;; ;; goal with explicit heaplets
;; (assert (not
;;         (=> (and (sdlst hx) (= hx (cons x xs)))
;;             (=> (ite (= x nil) (= ret nil) (= ret (nxt x)))
;;                 (ite (= ret nil) (dlst empty)
;;                       (and (dlst xs) (slst xs) (= (head xs) ret)))))
;; ))

(check-sat)
