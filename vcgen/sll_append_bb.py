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

program = """
(Const nil Loc)
(Var x Loc)
(Var y Loc)
(Var ret Loc)
(Var nxt Loc)
(Var tmp Loc)
(Var oldkeys_x SetInt)
(Var oldkeys_y SetInt)
(Function next Loc Loc)
(Function key Loc Int)

(RecFunction List Loc Bool)
(RecFunction Keys Loc SetInt)
(RecDef (List x) (ite (= x nil) True (and (List (next x)) (not (IsMember x (Sp (List (antiSp (next x))))))  ) ))
(RecDef (Keys x) (ite (= x nil) EmptySetInt (SetAdd (Keys (next x)) (key x)) ))

(Program sll_append (x y ret))
(Pre (and
(= oldkeys_x (Keys x))
(= oldkeys_y (Keys y))
(List x)
(List y)
(= (SetIntersect (Sp (List x)) (Sp (List y))) EmptySetLoc)
))
(Post (and
(List ret)
(= (Keys ret) (SetUnion oldkeys_x oldkeys_y))
))

(If (= x nil)
Then
(assign ret y)
(return)
Else
(call sll_append ((next x) y tmp)
(assign (next x) tmp)
(assignt ret x)
(return)
)
"""

bbgen_object = BBGenerator()
parsed_bbs = bbgen_object.parse_input(program)
print(f'{str(len(parsed_bbs))} Basic Blocks\n', '\n'.join(parsed_bbs[0]))


vc(parsed_bbs[0])