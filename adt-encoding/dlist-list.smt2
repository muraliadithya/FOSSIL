(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun nxt (Int) Int)
(declare-fun prv (Int) Int)

(declare-fun lst (ListOfLoc) Bool)
(assert (lst empty))
(assert (forall ((k Int) (x ListOfLoc)) (= (lst (cons k empty)) (= (nxt k) nil))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc)) (= (lst (cons k1 (cons k2 x))) (and (= (nxt k1) k2) (lst (cons k2 x))))  
))

(declare-fun dlst (ListOfLoc) Bool)
(assert (dlst empty))
(assert (forall ((k Int) (x ListOfLoc)) (= (dlst (cons k empty)) (= (nxt k) nil))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc)) (= (dlst (cons k1 (cons k2 x))) (and (= (nxt k1) k2) (= (prv k2) k1) (dlst (cons k2 x))))  
))

(declare-fun hx () ListOfLoc)
(declare-fun x () Int)
(declare-fun xs () ListOfLoc)
(declare-fun ret () Int)
(declare-fun rets () ListOfLoc)

;; faithful encoding

;; goal -- madhu's encoding: hangs, doesn't go through when lemma given
(assert (not
	(=> (and (dlst hx) (= hx (cons x xs)))
	    (=> (ite (= x nil) (= ret nil) (= ret (nxt x)))
                (exists ((hret ListOfLoc))
                        (and (lst hret) (= hret (cons ret rets))))))
))

;; uncommenting below goes through using cvc4+ig (need lemma assumed)

;; ;; lemma
;; (assert (forall ((hx ListOfLoc)) (=> (dlst hx) (lst hx))))

;; ;; goal -- madhu's encoding: hangs, doesn't go through when lemma given
;; (assert (not
;;         (=> (and (dlst hx) (= hx (cons x xs)))
;;             (=> (ite (= x nil) (= ret nil) (= ret (nxt x)))
;; 	    	(ite (= ret nil) (lst empty)
;; 		     (and (lst xs) (= (head xs) ret))))))
;; ))

(check-sat)
