(synth-fun lemma ((x Int) (y Int) (zero Int)) Bool

           ((Start Bool) (I Int) (I1 Int) (ILeaf Int))

           ((Start Bool (
                   (=> Start Start)
                   (= I I)
                   (nat y)
                   ))
            (I Int (I1
               (mult I1 I1)
                    (mult I1 I1)`
               (succ I1)
               ))
            (I1 Int (ILeaf
                (mult ILeaf ILeaf)
                (succ ILeaf)
                ))
            (ILeaf Int (x y zero))
            )

)

(synth-fun rswitch () Int

           ((Start Int))

           ((Start Int (0)))

)
