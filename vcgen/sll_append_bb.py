from BBGenerator import BBGenerator
import argparse
import importlib
from interpreting import vc  
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
(Const nil Loc)
(Var x Loc)
(Var y Loc)
(Var ret Loc)
(Var nxt Loc)
(Var tmp Loc)

(Function next Loc Loc nil)
(Function key Loc Int (IntConst 0))

(RecFunction List Loc Bool)
(RecFunction Keys Loc SetInt)
(RecDef (List x) (ite (= x nil) True (and (List (next x)) (not (IsMember x (Sp (List (antiSp (next x))))))  ) ))
(RecDef (Keys x) (ite (= x nil) EmptySetInt (SetAdd (Keys (next x)) (key x)) ))

(lemma (x) (= (Sp (Keys x)) (Sp (List x))))

(Var aux Loc)
(Var oldkeysx SetInt)
(Var oldkeysy SetInt)
(Var oldkeysaux SetInt)
(Program sll_append (x y oldkeysx oldkeysy ret))
(Pre (and
(= oldkeysx (Keys x))
(= oldkeysy (Keys y))
(List x)
(List y)
(= (SetIntersect (Sp (List x)) (Sp (List y))) EmptySetLoc)
))
(Post (and
(List ret)
(= (Keys ret) (SetUnion oldkeysx oldkeysy))
))

(If (= x nil)
Then
(assign ret y)
(return)
Else
(assign aux (next x))
(assign oldkeysaux (Keys aux))
(call sll_append (aux y oldkeysaux oldkeysy tmp))
(assign (next x) tmp)
(assign ret x)
(return)
)
"""

bbgen_object = BBGenerator()
parsed_bbs = bbgen_object.parse_input(real_prog)
i = 2


print(f'{str(len(parsed_bbs))} Basic Blocks\n', '\n'.join(parsed_bbs[i]))


vc(parsed_bbs[i])