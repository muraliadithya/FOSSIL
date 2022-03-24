import pyparsing as pp

from vcgen.parser import Program
from vcgen.parser import vardict, funcdict, recdefdict


ProgramText = pp.original_text_for(Program)

# pgm = """
# Var x Loc
# Var y Loc
# Var nil Loc
# Function next Loc Loc
# Function prev Loc Loc
# RecFunction list Loc Bool
# RecFunction SPlist Loc SetLoc
# RecFunction dlist Loc Bool
# RecFunction SPdlist Loc SetLoc
#
# Def list(x) := (If (x == nil) Then True Else list(next(x)))
# Def SPlist(x) := (If (x == nil) Then empSetLoc Else (x | SPlist(next(x))))
#
# Def dlist(x) := (If (x == nil) Then True Else ((next(prev(x)) == x) & dlist(next(x))))
# Def SPdlist(x) := (If (x == nil) Then empSetLoc Else (x | SPdlist(next(x))))
#
# @pre: dlist(x)
# assume (x != nil)
# assume (x.next != nil)
# x.next.next := x.next
# @post: list(x)
# """
#
# for parse_elem in ProgramText.parse_string(pgm):
#     print(parse_elem)
#
# # These represent states of the program at the end of parsing. Not correct yet since
# # actions have not been implemented for program statements
# print(vardict)
# print(funcdict)
# print(recdefdict)


# Use this command to read from a file instead
filename = 'tests/example.fsl'
for parse_elem in ProgramText.parse_file(filename):
    print(parse_elem)

print('\nParsing Successful!\n')
