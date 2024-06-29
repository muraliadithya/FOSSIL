from BBGenerator import BBGenerator
import argparse
import importlib
from interpreting_vcalt import vc  
# define set-fun keys^(x):
#   (case (x l= nil): emptyset;
#    case ((x |-> loc next: nxt; int key: ky) * true): 
#     ((singleton ky) union keys^(nxt));
#    default: emptyset
#   ) ; */
# // --------------------------------------------------------------
# _(dryad)
# SNnode * sll_append(SNnode * x1, SNnode * x2)
#   /*D_requires (sll^(x1) * sll^(x2)) */
#   /*D_ensures  (sll^(ret) & (keys^(ret) s= (old(keys^(x1)) union old(keys^(x2))))) */
# {
# 	if (x1 == NULL) {
# 		return x2;
# 	} else {
# 		SNnode * tmp = sll_append(x1->next, x2);
# 		x1->next = tmp;
# 		return x1;
# 	}	
# }

real_prog = """
(Function key   Loc Int)
(Function color Loc Int)
(Function left  Loc Loc)
(Function right Loc Loc)


(EqSp (Keys (Min Max BST BH RBT)))

(RecFunction Keys Loc SetInt)
(RecFunction Min  Loc Int)
(RecFunction Max  Loc Int)
(Var plus_infty Int)
(Var minus_infty Int)

(RecFunction Black Loc Bool)
(RecFunction BH Loc Int)

(RecFunction BST  Loc Bool)
(RecFunction RBT  Loc Bool)

(Var x Loc)




(RecDef (Min x) (ite (= x nil) plus_infty
                (ite (<= (key x) (Min (left x)))
                  (ite (<= (key x) (Min (right x)))
                    (key x)
                    (Min (right x))
                  )
                  (ite (<= (Min (left x)) (Min (right x)))
                    (Min (left x))
                    (Min (right x))
                  )
                )))
(RecDef (Max x) (ite (= x nil) minus_infty
                (ite (>= (key x) (Max (left x)))
                  (ite (>= (key x) (Max (right x)))
                    (key x)
                    (Max (right x))
                  )
                  (ite (>= (Max (left x)) (Max (right x)))
                    (Max (left x))
                    (Max (right x))
                  )
                )))

(RecDef (Black x) (ite (= x nil) True (= (color x) (IntConst 1))))
(RecDef (BH x) (ite (= x nil) (IntConst 1)
               (ite (Black x)
                    (+ (IntConst 1)
                      (ite (< (BH (left x)) (BH (right x)))
                        (BH (right x)) (BH (left x))))
                    (ite (< (BH (left x)) (BH (right x)))
                      (BH (right x)) (BH (left x))))))

(RecDef (BST x) (ite (= x nil) True
                     (and (< minus_infty (key x)) (< (key x) plus_infty)
                          (BST (left x))  (< (Max (left x)) (key x))
                          (BST (right x)) (< (key x) (Min (right x)))
                          (not (IsMember x (Sp (BST (antiSp (left x))))))
                          (not (IsMember x (Sp (BST (antiSp (right x))))))
                          (= EmptySetLoc (SetIntersect
                            (Sp (BST (antiSp (left x))))
                            (Sp (BST (antiSp (right x)))))) )))
(RecDef (RBT x) (ite (= x nil) True
                     (and (BST x) (RBT (left x)) (RBT (right x))
                          (= (BH (left x)) (BH (right x)))
                          (ite (Black x) True
                            (and (Black (left x)) (Black (right x)))) )))

(RecDef (Keys x) (ite (= x nil) EmptySetInt
                      (SetAdd (SetUnion (Keys (left x)) (Keys (right x)))
                              (key x))))

(lemma (x) (=> (RBT x) (=> (not (= x nil))
                          (not (IsMember x (Sp (RBT (antiSp (left x)))))))))
(lemma (x) (=> (RBT x) (=> (not (= x nil))
                          (not (IsMember x (Sp (RBT (antiSp (right x)))))))))

(Var k Int)
(Var ret Loc)
(Var tmp Loc)
(Var aux Loc)
(Var tmp1 Loc)

(Program rbt_insert_helper (x k) (ret))
(Pre (and (RBT x) (< minus_infty k) (< k plus_infty) ))
(Post (and (BST ret) (= (Keys ret) (SetAdd (Old (Keys x)) k))
           (ite (< k (Old (Min x))) (= (Min ret) k) (= (Min ret) (Old (Min x))))
           (ite (> k (Old (Max x))) (= (Max ret) k) (= (Max ret) (Old (Max x))))
           (= (BH ret) (Old (BH x))) (RBT (left ret)) (RBT (right ret))
           (= (BH (left ret)) (BH (right ret)))
           (ite (Black ret) True
             (ite (Old (Black x)) (and (Black (left ret)) (Black (right ret)))
                (or (Black (left ret)) (Black (right ret)))))
                 ))

(If (= x nil)
 Then
  (alloc ret)
  (assume (not (= ret nil)))
  (assign (key ret) k)
  (assign (color ret) (IntConst 0))
  (assign (left ret) nil)
  (assign (right ret) nil)
  (return)
 Else (If (= k (key x))
 Then
  (assign ret x)
  (return)
 Else (If (< k (key x))
 Then
  (assign aux (left x))
  (call rbt_insert_helper (aux k) (tmp))
  (If (or (Black tmp) (and (Black (left tmp)) (Black (right tmp))))
   Then
    (assign (left x) tmp)
    (assign ret x)
    (return)
   Else
    (If (not (Black (left tmp)))
     Then
      (assign tmp1 (right tmp))
      (assign (left x) (right tmp))
      (assign (right tmp) x)
      (assign tmp1 (left tmp))
      (assign (color tmp1) (IntConst 1))
      (assign ret tmp)
      (return)
     Else
      (assign ret (right tmp))
      (assign tmp1 (right ret))
      (assign (left x) tmp1)
      (assign tmp1 (left ret))
      (assign (right tmp) tmp1)
      (assign (left ret) tmp)
      (assign (right ret) x)
      (assign (color tmp) (IntConst 1))
      (return)
    )
  )
 Else
  (assign aux (right x))
  (call rbt_insert_helper (aux k) (tmp))
  (If (or (Black tmp) (and (Black (left tmp)) (Black (right tmp))))
   Then
    (assign (right x) tmp)
    (assign ret x)
    (return)
   Else
    (If (not (Black (left tmp)))
     Then
      (assign ret (left tmp))
      (assign tmp1 (left ret))
      (assign (right x) tmp1)
      (assign tmp1 (right ret))
      (assign (left tmp) tmp1)
      (assign (left ret) x)
      (assign (right ret) tmp)
      (assign (color tmp) (IntConst 1))
      (return)
     Else
     (assign tmp1 (left tmp))
      (assign (right x) tmp1)
      (assign (left tmp) x)
      (assign tmp1 (right tmp))
      (assign (color tmp1) (IntConst 1))
      (assign ret tmp)
      (return)
    )
  )
)))

(Program rbt_insert (x k) (ret))
(Pre (and (RBT x) (< minus_infty k) (< k plus_infty) ))
(Post (and (RBT ret) (= (Keys ret) (SetAdd (Old (Keys x)) k))
           (ite (< k (Old (Min x))) (= (Min ret) k) (= (Min ret) (Old (Min x))))
           (ite (> k (Old (Max x))) (= (Max ret) k) (= (Max ret) (Old (Max x)))) ))

(call rbt_insert_helper (x k) (ret))
(assign (color ret) (IntConst 1))
(return)

"""

bbgen_object = BBGenerator()
parsed_bbs = bbgen_object.parse_input(real_prog)
i = 3


print(f'{str(len(parsed_bbs))} Basic Blocks\n', '\n'.join(parsed_bbs[i]))


vc(parsed_bbs[i], logic='fl', onthefly=False)