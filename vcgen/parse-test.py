import pyparsing as pp
from vcgen.parser import Program
from vcgen.parser import vardict, funcdict, recdefdict, trans


ProgramText = pp.original_text_for(Program)

# # Use this command to read the input from a file
# filename = 'tests/example.fsl'
# for parse_elem in ProgramText.parse_file(filename):
#     print(parse_elem)

# print('\nParsing Successful!\n')


# You can also make a string within python and use parse_string instead of parse_file
pgm = """
Var x0 Loc
Var y0 Loc
Var z Loc
Const nil Loc

Function next0 Loc Loc
RecFunction list Loc Bool

Def list(z) := (If (z == nil) Then True Else list(next0(z)))

@pre: list(x0)
//Assume only var assign atm.
assume (!(x0!= nil))
assume (x0==y0)



@post: list(x0)
"""

# for parse_elem in ProgramText.parse_string(pgm):
#     print(parse_elem)
#     print('------------------------\n')
ProgramText.parse_string(pgm)
    
print('\n\n\n\n')
# These represent states of the program at the end of parsing. Not correct yet since
# actions have not been implemented for program statements
print(vardict)
print('\n')
print(funcdict)
print('\n')
print(recdefdict)
print('\n',trans)

