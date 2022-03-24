import pyparsing as pp

from vcgen.parser import Program
from vcgen.parser import vardict, funcdict, recdefdict


ProgramText = pp.original_text_for(Program)
pgm = """
Var x Loc
Var y Loc
Var nil Loc
Function next Loc Loc
Function prev Loc Loc
RecFunction list Loc Bool
RecFunction SPlist Loc SetLoc
RecFunction dlist Loc Bool
RecFunction SPdlist Loc SetLoc

Def list(x) := ((x == nil) | ((x != nil) & list(next(x))))
Def SPlist(x) := (If (x == nil) Then empSetLoc Else (x | SPlist(next(x))))

Def dlist(x) := ((x == nil) | ((x != nil) & ((next(prev(x)) == x) & dlist(next(x)))))
Def SPdlist(x) := (If (x == nil) Then empSetLoc Else (x | SPdlist(next(x))))

@pre: dlist(x)
assume (x != nil)
assume (x.next != nil)
x.next.next := x.next
@post: list(x)
"""

for parse_elem in ProgramText.parse_string(pgm):
    print(parse_elem)

print(vardict)
print(funcdict)
print(recdefdict)
