from BBGenerator import BBGenerator
import argparse
import importlib
from interpreting import vc
# /*D_defs
# define pred dll^(x):
#  (
#    (((x l= nil) & emp) |

#     ((x |-> loc next: y) & (y l= nil))) |

#      (
#           (((x |-> loc next: nxt) * (nxt |-> secondary prev: x)) * true) &
#           (  (x |-> loc next: nxt) * ((~(nxt l= nil)) & dll^(nxt)) )
#     )
#  );
  
# define set-fun keys^(x):
#   (case (x l= nil): emptyset;
#    case ((x |-> loc next: nxt; int key: ky) * true): 
#     ((singleton ky) union keys^(nxt));
#    default: emptyset
#   ) ; */
# // -------------------------------------------------------------- 

# _(dryad)
# DLNode * dll_append(DLNode * x1, DLNode * x2) 
#   /*D_requires (dll^(x1) * dll^(x2)) */
#   /*D_ensures  (dll^(ret) & (keys^(ret) s= (old(keys^(x1)) union old(keys^(x2))))) */
# {
#   if (x1 == NULL) {
#     return x2;
#   } else {
#     DLNode * tmp = dll_append(x1->next, x2);
#     x1->next = tmp;
#     if (tmp) tmp->prev = x1;
#     return x1;
#   }
# }

#folding 2
#without lemma slow on depth 2
real_prog = """
(Var x Loc)
(Var y Loc)
(Var nxt Loc)
(Var tmp Loc)
(Var ret Loc)

(Function next Loc Loc)
(Function prev Loc Loc)
(Function key Loc Int)
(RecFunction Dll Loc Bool)
(RecFunction Keys Loc SetInt)
(RecDef (Dll x) (ite (= x nil) True (ite (= (next x) nil) True
                                    (and (= x (prev (next x))) (Dll (next x)) (not (IsMember x (Sp (Dll (antiSp (next x)))))) ) 
                                    )
                )
)


(RecDef (Keys x) (ite (= x nil) EmptySetInt (SetAdd (Keys (next x)) (key x)) ))

(Var aux Loc)
(Var oldkeysx SetInt)
(Var oldkeysy SetInt)
(Var oldkeysaux SetInt)

(lemma (x) (= (Sp (Keys x)) (Sp (Dll x))))

(Program dll_append (x y oldkeysx oldkeysy ret))
(Pre (and
(Dll x) (Dll y)
(= EmptySetLoc (SetIntersect (Sp (Dll x)) (Sp (Dll y))))
(= oldkeysx (Keys x))
(= oldkeysy (Keys y))
))
(Post (and
(Dll ret)
(= (Keys ret) (SetUnion oldkeysx oldkeysy))
))

(If (= x nil)
Then
(assign ret y)
(return)
Else
(assign aux (next x))
(assume (= oldkeysaux (Keys aux)))
(call dll_append (aux y oldkeysaux oldkeysy tmp))
(assign (next x) tmp)
(assign (prev tmp) x)
(assign ret x)
(return)
)
"""



bbgen_object = BBGenerator()
parsed_bbs = bbgen_object.parse_input(real_prog)
i = 2

print(f'{str(len(parsed_bbs))} Basic Blocks\n', '\n'.join(parsed_bbs[i]))


vc(parsed_bbs[i])