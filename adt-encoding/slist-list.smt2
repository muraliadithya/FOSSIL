(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; vars and unint functions
(declare-fun nil () Int)
(declare-fun ret () ListOfLoc)

(declare-fun nxt (Int) Int)
(declare-fun key (Int) Int)

;; recdefs
(declare-fun lst (ListOfLoc) Bool)
(declare-fun slst (ListOfLoc) Bool)

(assert (lst empty))
(assert (forall ((k Int) (x ListOfLoc)) 
	(= (lst (cons k empty)) 
	   (= (nxt k) nil))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc)) 
	(= (lst (cons k1 (cons k2 x))) 
	   (and (= (nxt k1) k2) (lst (cons k2 x))))
))

(assert (slst empty))
(assert (forall ((k Int) (x ListOfLoc)) 
	(= (slst (cons k empty)) (= (nxt k) nil))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc)) 
	(= (slst (cons k1 (cons k2 x))) 
	   (and (= (nxt k1) k2) (<= (key k1) (key k2)) (slst (cons k2 x))))
))

;; goal
(assert (not 
(forall ((x ListOfLoc) (k Int) (xs ListOfLoc) (ret ListOfLoc))
	(=> (slst x) 
	    (=> (ite (= x empty) (= ret empty) 
                     (and (= x (cons k xs)) (= ret xs))) (lst ret))))
))
(check-sat)
