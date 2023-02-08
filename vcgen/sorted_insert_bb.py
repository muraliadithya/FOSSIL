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
# {

# 	if (x == NULL) {
# 		SNnode * tail = (SNnode *) malloc(sizeof(SNnode));
# 		_(assume tail != NULL)

# 		tail->key = k;
# 		tail->next = NULL;

# 		return tail;
# 	} 
# 	else if (k > x->key) {
# 		SNnode * tmp = sorted_insert(x->next, k);
# 		x->next = tmp;
# 		return x;
# 	} 
# 	else {

# 		SNnode * head = (SNnode *) malloc(sizeof(SNnode));
# 		_(assume head != NULL)

# 		head->key = k;
# 		head->next = x;

# 		return head;
# 	}
# }

real_prog = """
(Const nil Loc)
(Var x Loc)
(Var k Int)
(Var ret Int)
(Var tmp Loc)

(Function next Loc Loc)
(Function key Loc Int)
(RecFunction Sorted Loc Bool)
(RecFunction Keys Loc SetInt)

(Var plus_infty Int)
(RecFunction Min Loc Int)
(RecDef (Min x) (ite (= x nil) plus_infty (ite (< (key x) (Min (next x))) (key x) (Min (next x)) ) ))


(RecDef (Sorted x) (ite (= x nil) True (and (Sorted (next x)) (not (IsMember x (Sp (Sorted (antiSp (next x)))))) (<= (key x) (Min (next x))) )))
(RecDef (Keys x) (ite (= x nil) EmptySetInt (SetAdd (Keys (next x)) (key x) ) ))

(Var oldkeysx SetInt)
(Var aux Loc)
(Var oldkeysaux SetInt)
(Var oldnxt Loc)

(lemma (x) (< (key x) plus_infty))
(lemma (x) (=> (Sorted x) (= (SPKeys x) (SPSorted x)) ))

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
(return)
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
    (return)
    Else
    (alloc tmp)
    (assume (not (= tmp nil)))
    (assign (key tmp) k)
    (assign (next tmp) x)
    (assign ret tmp)
    (return)
    )
)
(return)
"""



bbgen_object = BBGenerator()
parsed_bbs = bbgen_object.parse_input(real_prog)


i = 3


print(f'{str(len(parsed_bbs))} Basic Blocks\n', '\n'.join(parsed_bbs[i]))
vc(parsed_bbs[i])