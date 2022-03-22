(set-logic ALL_SUPPORTED)

;; heap
(declare-datatypes () ((ListOfLoc (cons (head Int) (tail ListOfLoc)) (empty))))

;; unint functions
(declare-fun nil () Int)
(declare-fun nxt (Int) Int)

;; recdefs
(declare-fun lseg (ListOfLoc Int) Bool)
(declare-fun cyclic (ListOfLoc) Bool)

(assert (forall ((y Int)) (lseg empty y)))
(assert (forall ((k Int) (y Int))
        (= (lseg (cons k empty) y)
           (= (nxt k) y))
))
(assert (forall ((k1 Int) (k2 Int) (x ListOfLoc) (y Int))
        (= (lseg (cons k1 (cons k2 x)) y)
           (and (= (nxt k1) k2) (lseg (cons k2 x) y)))
))

(assert (forall ((x ListOfLoc)) (= (cyclic x) (lseg (tail x) (head x)))))

(declare-fun hx () ListOfLoc)
(declare-fun x () Int)
(declare-fun xs () ListOfLoc)

;; lemma
(assert (forall ((hx ListOfLoc) (y Int)) 
        (=> (and (lseg hx y) (not (= y nil))) (lseg hx (nxt y)))))

;; goal
(assert (not
        (=> (and (cyclic hx) (= hx (cons x xs)))
            (exists ((hret ListOfLoc))
                    (and (cyclic hret) (= hret xs))))
))

(check-sat)
