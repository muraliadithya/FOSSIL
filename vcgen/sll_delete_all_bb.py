from BBGenerator import BBGenerator
import argparse
import importlib
from interpreting import vc  


# _(dryad)
# SNnode * sll_delete_all(SNnode * x, int k)
#   /*D_requires sll^(x) */
#   /*D_ensures (sll^(ret) & (((k i-in old(keys^(x))) => (keys^(ret) s= (old(keys^(x)) setminus (singleton k)))) &
#                  ((~ (k i-in old(keys^(x)))) => (keys^(ret) s= old(keys^(x)))))) */
# {
# 	if (x == NULL) {
# 		return x;
# 	} else if (x->key == k) {
# 		SNnode * tmp = sll_delete_all(x->next, k);
# 		free(x);
# 		return tmp;
# 	} else {
# 		SNnode * tmp = sll_delete_all(x->next, k);
# 		x->next = tmp;
# 		return x;
# 	}
# }

program = """
(Const nil Loc)
(Var x Loc)
(Var y Loc)
(Var ret Loc)
(Var nxt Loc)
(Var tmp Loc)
(Var k Int)
(Var oldkeys_x SetInt)
(Var oldkeys_y SetInt)
(Function next Loc Loc)
(Function key Loc Int)

(RecFunction List Loc Bool)
(RecFunction Keys Loc SetInt)
(RecDef (List x) (ite (= x nil) True (and (List (next x)) (not (IsMember x (Sp (List (antiSp (next x))))))  ) ))
(RecDef (Keys x) (ite (= x nil) EmptySetInt (SetAdd (Keys (next x)) (key x)) ))

(Program sll_delete_all (x k ret))
(Pre (and
(List x)
(= oldkeys_x (Keys x))
))

(Post (and
(List ret)
(ite (IsMember k oldkeys_x) (= (Keys ret) (SetDel oldkeys_x k)) (= (Keys ret oldkeys_x)) )
))

(If (= x nil)
Then
(assign ret x)
(return)
Else
    (If (= (key x) k)
    Then
    (call sll_delete_all ((next x) k tmp))
    (free x)
    (assign ret tmp)
    (return)
    Else
    (call sll_delete_all ((next x) k tmp))
    (assign (next x) tmp)
    (assign ret x)
    (return)
    )
)
"""

bbgen_object = BBGenerator()
parsed_bbs = bbgen_object.parse_input(program)
print(f'{str(len(parsed_bbs))} Basic Blocks\n', '\n'.join(parsed_bbs[0]))


vc(parsed_bbs[0])