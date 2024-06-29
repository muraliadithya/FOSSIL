from interpreting_vcalt import vc 


f = open("tmp/rbt_insert (1)/bb4.fsl", "r")
ip = f.readlines()

vc(ip, logic = 'sl', onthefly = True)

# (Post (and (BST ret) (= (Keys ret) (SetAdd (Old (Keys x)) k))
#            (ite (< k (Old (Min x))) (= (Min ret) k) (= (Min ret) (Old (Min x))))
#            (ite (> k (Old (Max x))) (= (Max ret) k) (= (Max ret) (Old (Max x))))
#            (= (BH ret) (Old (BH x))) 
           
#            (RBT (left ret)) (RBT (right ret))
#            (= (BH (left ret)) (BH (right ret)))
#            (ite (Black ret) True
#              (ite (Old (Black x)) (and (Black (left ret)) (Black (right ret)))
#                 (or (Black (left ret)) (Black (right ret)))))
#                  ))




# (RecDef (RBT x) (ite (= x nil) True
#                      (and (BST x) (RBT (left x)) (RBT (right x))
#                           (= (BH (left x)) (BH (right x)))
#                           (ite (Black x) True
#                             (and (Black (left x)) (Black (right x)))) )))

# (RecDef (RBT x) (ite (= x nil) True
#                   (and  (BST x) (and (= (BH (left x)) (BH (right x)))
#                                  (Exists (= lft (left x)) 
#                                     (Exists (= rht (right x))
#                                         (Exists (= cl (color lft)) 
#                                               (Exists (= cr (color rht))
#                                                   (*
#                                                    (ite (Black x) True
#                                                       (and (ite (= lft nil) True (= cl (IntConst 1)))
#                                                             (ite (= rht nil) True (= cr (IntConst 1))))   
#                                                    )
#                                          (* (RBT lft) (RBT rht))
#                                       )
#                                     ))))      
#                    ))
# ))





#  (RecDef (Sorted x) (ite (= x nil) True
#                     (Exists (= nxt (next x)) (Exists (= k (key x))
#                     (* (< k plus_infty) (*
#                       (= k (key x)) (and (Sorted nxt) (<= k (Min nxt)))))
#                     ))
#                ))
# (Exists (= k (f x)) A) := (= k (f x)) AND A[k<- (antiSp (f x))]
# Translated:
#  (RecDef (Sorted x) (ite (= x nil) True 
#                      (and (< (antiSp (key x)) plus_infty) 
#                       (and (= (antiSp (key x)) (key x)) 
#                        (and (Sorted (antiSp (next x))) 
#                         (<= (antiSp (key x)) (Min (antiSp (next x)))) 
#                         (= (Sp (Sorted (antiSp (next x)))) (Sp (<= (antiSp (key x)) (Min (antiSp (next x))))))) 
#                         (= EmptySetLoc (SetIntersect (Sp (= (antiSp (key x)) (key x))) 
#                                                 (Sp (and (Sorted (antiSp (next x))) 
#                                                     (<= (antiSp (key x)) (Min (antiSp (next x)))) 
#                                                     (= (Sp (Sorted (antiSp (next x)))) (Sp (<= (antiSp (key x)) (Min (antiSp (next x))))))))))) 
#                         (= EmptySetLoc (SetIntersect (Sp (< (antiSp (key x)) plus_infty)) 
#                                         (Sp (and (= (antiSp (key x)) (key x)) (and (Sorted (antiSp (next x))) 
#                                                                                (<= (antiSp (key x)) (Min (antiSp (next x)))) 
#                                                                                (= (Sp (Sorted (antiSp (next x)))) (Sp (<= (antiSp (key x)) 
#                                                                                 (Min (antiSp (next x))))))) 
#                                 (= EmptySetLoc (SetIntersect (Sp (= (antiSp (key x)) (key x))) (Sp (and (Sorted (antiSp (next x))) 
#                                 (<= (antiSp (key x)) (Min (antiSp (next x)))) (= (Sp (Sorted (antiSp (next x)))) (Sp (<= (antiSp (key x)) (Min (antiSp (next x)))))))))))))))))


#                         (= EmptySetLoc (SetIntersect (Sp (= Empty (key x))) 
#                                                 (Sp (and (Sorted Empty)
#                                                     (<= Empty (Min Empty)) 
#                                                     (= (Sp (Sorted Empty)))) (Sp (<= Empty (Min Empty))))))

# (= Empty Empty)

