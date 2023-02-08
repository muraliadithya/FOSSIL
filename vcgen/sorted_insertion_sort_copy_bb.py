from BBGenerator import BBGenerator
import argparse
import importlib
from interpreting import vc
# typedef
# /*D_tag node */
# struct node {
#   int key;
#   struct node * next;
# } SNnode;

# /*D_defs
# define pred sorted^(x): 
#   ( 
#   ((x l= nil) & emp) | 
#   ((x |-> loc next: nxt; int key: ky) * 
#   (sorted^(nxt) & (ky lt-set keys^(nxt)))
#    )  
#   ) ;
  
# define set-fun keys^(x):
#   (case (x l= nil): emptyset;
#    case ((x |-> loc next: nxt; int key: ky) * true): 
#     ((singleton ky) union keys^(nxt));
#    default: emptyset
#   ) ;*/
# // -------------------------------------------------------

# _(dryad)
# SNnode * sorted_insert(SNnode *x, int k)
#    /*D_requires sorted^(x) */
#    /*D_ensures (sorted^(ret) & (keys^(ret) s= (old(keys^(x)) union (singleton k)))) */


# _(dryad)
# SNnode * insertion_sort_copy(SNnode * l)
#   /*D_requires sll^(l) */
#   /*D_ensures ((sll^(ret) & sorted^(ret)) & (keys^(ret) s= old(keys^(l)))) */
# {
# 	if (l == NULL) {
# 		return l;
# 	} else {
# 		SNnode * tl = insertion_sort_copy(l->next);

# 		SNnode * nl = sorted_insert(tl, l->key);
# 		return nl;
# 	}
# }


real_prog = """
(Const nil Loc)
(Var x Loc)
(Var k Int)
(Var ret Int)
(Var tmp Loc)
(Var tmp2 Loc)

(Function next Loc Loc)
(Function key Loc Int)
(RecFunction Sorted Loc Bool)
(RecFunction Keys Loc SetInt)

(Var plus_infty Int)
(RecFunction Min Loc Int)
(RecDef (Min x) (ite (= x nil) plus_infty (ite (< (key x) (Min (next x))) (key x) (Min (next x)) ) ))


(RecDef (Sorted x) (ite (= x nil) True (and (Sorted (next x)) (not (IsMember x (Sp (Sorted (antiSp (next x)))))) (<= (key x) (Min (next x))) )))
(RecDef (Keys x) (ite (= x nil) EmptySetInt (SetAdd (Keys (next x)) (key x) ) ))


(RecFunction List Loc Bool)
(RecDef (List x) (ite (= x nil) True (and (List (next x)) (not (IsMember x (Sp (List (antiSp (next x))))))) ))

(Var oldkeysx SetInt)
(Var aux Loc)
(Var intaux Loc)
(Var oldkeysaux SetInt)
(Var oldnxt Loc)
(Var oldkeystmp SetInt)

(lemma (x) (< (key x) plus_infty))
(lemma (x) (=> (Sorted x) (= (SPKeys x) (SPSorted x)) ))
(lemma (x) (=> (Sorted x) (List x)))

(Program sorted_insert (x k oldkeysx ret))
(Pre (Sorted x))
(Post (and
(Sorted ret)
(= (Keys ret) (SetAdd oldkeysx k))
))

(assume (= oldkeysx (Keys x)) )
(If (= x nil)
Then
(alloc tmp)
(assume (not (= tmp nil)))
(assign (key tmp) k)
(assign (next tmp) nil)
(assign ret tmp)
Else
    (If (< (key x) k)
    Then
    (assign aux (next x))
    (assign oldkeysaux (Keys aux))
    (assign oldnxt (next x))
    (call sorted_insert (aux k oldkeysaux tmp))
    (assume (=> (IsSubset (Old (Keys oldnxt)) (Keys tmp)) (<= (Old (Min oldnxt)) (Min tmp))))
    (assign (next x) tmp)
    (assign ret x)
    Else
    (alloc tmp)
    (assume (not (= tmp nil)))
    (assign (key tmp) k)
    (assign (next tmp) x)
    (assign ret tmp)
    )
)
(return)

(Program insertion_sort_copy (x oldkeysx ret))
(Pre (List x))
(Post (and
(List ret)
(Sorted ret)
(= (Keys ret) oldkeysx)
))

(assume  (= oldkeysx (Keys x)))
(If (= x nil)
Then
(assign ret x)
Else
(assign aux (next x))
(assume  (= oldkeysaux (Keys aux)))
(call insertion_sort_copy (aux oldkeysaux tmp))
(assign intaux (key x))
(assign oldkeystmp (Keys tmp))
(call sorted_insert (tmp intaux oldkeystmp tmp2))
(assign ret tmp2)
)
(return)
"""



bbgen_object = BBGenerator()
parsed_bbs = bbgen_object.parse_input(real_prog)
i = 7


print(f'{str(len(parsed_bbs))} Basic Blocks\n', '\n'.join(parsed_bbs[i]))


vc(parsed_bbs[i])