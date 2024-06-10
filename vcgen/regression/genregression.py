bench_template_1 = """

(Var x Loc)
(Var xp Loc)
(Var h Loc)

(Function next Loc Loc)
(Function key  Loc Int)

(RecFunction List Loc Bool)
(RecDef (List x) (ite (= x nil) True
                      (and (List (next x))
                           (not (IsMember x (Sp (List (antiSp (next x)))))))))

(Program regression (x) (h))
(Pre (List x))
(Post (List h))
(assign xp x)
(assign h x)
{}
(return)
"""


repeated_text_1 = """
(assume (not (= xp nil)))
(assign xp (next xp))
(assign (next h) xp)
"""

import sys
repetition = int(sys.argv[1])
if repetition <= 0:
    raise ValueError("Number of repetitions must be positive")


bench_template = bench_template_1
repeated_text = repeated_text_1

program = bench_template.format(repeated_text*repetition)

#print(program)

with open('reg.fsl','w') as fh:
    fh.write(program)
