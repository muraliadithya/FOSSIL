from BBGenerator import BBGenerator
import argparse
import importlib
from interpreting import vc

real_prog = """
(Const nil Loc)
(Var x Loc)
(Var y Loc)

(Var head Loc)
(Var tail Loc)
(Var nxt Loc)
(Var ret Loc)
(Var new_nxt Loc)
(Var hd_nxt Loc)
(Function next Loc Loc)
(RecFunction Lseg Loc Loc Bool)
(RecDef (Lseg x y) (ite (= x y) True (and (Lseg (next x) y) (not (IsMember x (Sp (Lseg (antiSp (next x)) y)))))   )    )


(Program lseg_delete_back (head tail ret))
(Pre (and
(not (= head nil))
(Lseg head tail)
))
(Post (Lseg ret tail))

(assign nxt (next head))
(assume (not (= head tail)))
(If (= nxt nil)
Then
(assign ret nxt)
(free head)
(return)
Else
    (If (= nxt tail)
    Then
    (free head)
    (assign ret tail)
    (return)
    Else
    (call lseg_delete_back (nxt tail hd_nxt))
    (assign (next head) hd_nxt)
    (assign ret head)
    (return)
    )
)
(return)
"""



bbgen_object = BBGenerator()
parsed_bbs = bbgen_object.parse_input(real_prog)
i =3


print(f'{str(len(parsed_bbs))} Basic Blocks\n', '\n'.join(parsed_bbs[i]))


vc(parsed_bbs[i])