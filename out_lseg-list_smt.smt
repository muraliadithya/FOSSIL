(set-logic ALL)

;; x = 0, y = 1, z = 2
;(declare-const x Int)
;(declare-const y Int)
;(declare-const z Int)
;(assert (= x 0))
;(assert (= y 1))
;(assert (= z 2))

;; combination of true models and false model
(define-fun next ((x!0 Int)) Int
  (ite (= x!0 8199) 8199
  (ite (= x!0 8200) 8200
  (ite (= x!0 8201) 8200
  (ite (= x!0 3199) 3199
  (ite (= x!0 3200) 3199
  (ite (= x!0 3201) 3201
  (ite (= x!0 21199) 21199
  (ite (= x!0 21200) 21199
  (ite (= x!0 21201) 21201
  (ite (= x!0 8349) 8350
  (ite (= x!0 8350) 8350
  (ite (= x!0 8351) 8350
  (ite (= x!0 3649) 3649
  (ite (= x!0 3650) 3649
  (ite (= x!0 3651) 3649
  (ite (= x!0 1499) 1499
  (ite (= x!0 1500) 1501
  (ite (= x!0 1501) 1501
  (ite (= x!0 10849) 10849
  (ite (= x!0 10850) 10849
  (ite (= x!0 10851) 10849
  (ite (= x!0 21399) 21400
  (ite (= x!0 21400) 21400
  (ite (= x!0 21401) 21401
  (ite (= x!0 19999) 19999
  (ite (= x!0 20000) 20000
  (ite (= x!0 20001) 19999
  (ite (= x!0 1) 1
  (ite (= x!0 0) 1
  (ite (= x!0 2) 4
  (ite (= x!0 4) 5
    12649))))))))))))))))))))))))))))))))
(define-fun list ((x!0 Int)) Bool
  (ite (= x!0 8199) false
  (ite (= x!0 3199) false
  (ite (= x!0 3200) false
  (ite (= x!0 21199) false
  (ite (= x!0 21200) false
  (ite (= x!0 1499) false
  (ite (= x!0 21399) false
  (ite (= x!0 21400) false
  (ite (= x!0 20000) false
  (ite (= x!0 2) false
  (ite (= x!0 4) false
    true))))))))))))
(define-fun lsegy ((x!0 Int)) Bool
  (or (= x!0 4)
      (= x!0 2)
      (= x!0 0)
      (= x!0 8199)
      (= x!0 3200)
      (= x!0 12650)
      (= x!0 21200)
      (= x!0 8349)
      (= x!0 3650)
      (= x!0 1499)
      (= x!0 10850)
      (= x!0 21399)
      (= x!0 21400)
      (= x!0 20000)))
(define-fun list_p ((x!0 Int)) Bool
  (ite (= x!0 8199) false
  (ite (= x!0 3199) false
  (ite (= x!0 3200) false
  (ite (= x!0 21199) false
  (ite (= x!0 8349) false
  (ite (= x!0 3650) false
  (ite (= x!0 20000) false
  (ite (= x!0 0) false
  (ite (= x!0 2) false
  (ite (= x!0 4) false
    true)))))))))))
(define-fun next_p ((x!0 Int)) Int
  (ite (= x!0 8199) 8199
  (ite (= x!0 8200) 8200
  (ite (= x!0 8201) 8200
  (ite (= x!0 3199) 3199
  (ite (= x!0 3200) 3199
  (ite (= x!0 3201) 3201
  (ite (= x!0 12649) 12649
  (ite (= x!0 12650) 12651
  (ite (= x!0 12651) 12649
  (ite (= x!0 21199) 21199
  (ite (= x!0 21200) 21201
  (ite (= x!0 21201) 21201
  (ite (= x!0 8349) 8349
  (ite (= x!0 8350) 8350
  (ite (= x!0 8351) 8350
  (ite (= x!0 3649) 3649
  (ite (= x!0 3650) 3650
  (ite (= x!0 3651) 3649
  (ite (= x!0 1499) 1500
  (ite (= x!0 1500) 1501
  (ite (= x!0 1501) 1501
  (ite (= x!0 21399) 21400
  (ite (= x!0 21400) 21401
  (ite (= x!0 21401) 21401
  (ite (= x!0 19999) 19999
  (ite (= x!0 20000) 20000
  (ite (= x!0 20001) 19999
  (ite (= x!0 1) 1
  (ite (= x!0 0) 3
  (ite (= x!0 2) 4
  (ite (= x!0 4) 5
    10849))))))))))))))))))))))))))))))))
(define-fun lsegy_p ((x!0 Int)) Bool
  (or (= x!0 0)
      (= x!0 8199)
      (= x!0 3200)
      (= x!0 12650)
      (= x!0 21200)
      (= x!0 8349)
      (= x!0 3650)
      (= x!0 1499)
      (= x!0 10850)
      (= x!0 21399)
      (= x!0 21400)
      (= x!0 20000)))

;; TODO: this should be generated from the problem parameters
;; lemma to synthesize
;(synth-fun lemma ((x Int) (nil Int) (y Int)) Bool
;           ((Start Bool) (Rec Bool) (B Bool) (I Int))
;
;           ((Start Bool
;                  ((=> Rec B)))
;           (Rec Bool
;                  ((list I) (lsegy I) (list_p I) (lsegy_p I)))
;           (B Bool
;                  ((=> B B)
;                   (and B B)
;                   (or B B)
;                   (not B)
;                   (list I) (lsegy I) (list_p I) (lsegy_p I)))
;            (I Int (x nil y
;                   (next I))))
;)

(define-fun lemma ((x Int)(nil Int)(y Int)) Bool
(=> (and (lsegy x) (list y)) (list x))
)

;; asserts from false model
(assert (or (not (lemma 1 1 0))
(not (lemma 0 1 0))
(not (lemma 2 1 0))
(not (lemma 4 1 0))
(not (lemma 4 1 0))
))

;; asserts from true models
(assert (or (lemma 8199 8200 8199)
(lemma 8200 8200 8199)
(lemma 8201 8200 8199)
))
(assert (or (lemma 3199 3201 3200)
(lemma 3200 3201 3200)
(lemma 3201 3201 3200)
))
(assert (or (lemma 12649 12649 12650)
(lemma 12650 12649 12650)
(lemma 12651 12649 12650)
))
(assert (or (lemma 21199 21201 21200)
(lemma 21200 21201 21200)
(lemma 21201 21201 21200)
))
(assert (or (lemma 8349 8350 8349)
(lemma 8350 8350 8349)
(lemma 8351 8350 8349)
))
(assert (or (lemma 3649 3649 3650)
(lemma 3650 3649 3650)
(lemma 3651 3649 3650)
))
(assert (or (lemma 1499 1501 1499)
(lemma 1500 1501 1499)
(lemma 1501 1501 1499)
))
(assert (or (lemma 10849 10849 10850)
(lemma 10850 10849 10850)
(lemma 10851 10849 10850)
))
(assert (or (lemma 21399 21401 21400)
(lemma 21400 21401 21400)
(lemma 21401 21401 21400)
))
(assert (or (lemma 19999 19999 20000)
(lemma 20000 19999 20000)
(lemma 20001 19999 20000)
))

(check-sat)