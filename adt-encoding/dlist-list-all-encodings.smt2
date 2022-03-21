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

;; lemma
;; (assert (forall ((hx ListOfLoc)) (=> (dlst hx) (lst hx))))

;; goal -- original encoding: goes through
;; (assert (not 
;; (forall ((x ListOfLoc) (ret ListOfLoc))
;; 	(=> (dlst x) 
;; 	    (=> (ite (= x empty) (= ret empty) (= ret (tail x))) (lst ret))))
;; ))

;; goal -- adithya's encoding: goes through
;; (assert (not 
;; (forall ((x ListOfLoc) (k Int) (xs ListOfLoc) (ret ListOfLoc))
;;         (=> (dlst x)
;;             (=> (ite (= x empty) (= ret empty) (and (= x (cons k xs)) (= ret xs))) (lst ret))))
;; ))

;; goal -- madhu's encoding: hangs, doesn't go through when lemma given
;; (assert (not 
;; (forall ((hx ListOfLoc) (x Int) (xs ListOfLoc) (ret Int) (rets ListOfLoc))
;; 	(=> (and (dlst hx) (= hx (cons x xs)))
;; 	    (=> (ite (= x nil) (= ret nil) (= ret (nxt x)))
;;                 (exists ((hret ListOfLoc))
;;                         (and (lst hret) (= hret (cons ret rets)))))))
;; ))

;; goal -- combined encoding: hangs, doesn't go through when lemma given
(assert (not 
(forall ((hx ListOfLoc) (x Int) (hret ListOfLoc) (ret Int))
        (=> (and (dlst hx) (= (head hx) x))
            (=> (ite (= x nil) (and (= ret nil) (= hret empty)) (and (= ret (nxt x)) (= hret (tail hx))))
                (and (lst hret) (= (head hret) ret)))))
))

(check-sat)
