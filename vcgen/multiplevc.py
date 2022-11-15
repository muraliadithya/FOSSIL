import importlib
from vcgen.parser import vc
import vcgen.parser
import sys
import os
import numpy as np
# Making swaptwo.fsl a 'default' argument during development.
# Must make this a full menu with appropriate arguments before release.
auxfile = 'vcgen/tests/aux.fsl'

with open(auxfile, 'r') as f:
    lines = f.readlines()

endl = 0
for i,l in enumerate(lines): 
    if l=='(END)\n' or l == '(END)':
        endl = i
        break
    elif i == len(lines)-1:
        endl = i+1
# print('file is:-', lines[:endl])
print(vc(lines[:endl]))

if endl<len(lines):
    print(lines[endl],'..',endl)
    lines = lines[endl+1:]
    open(auxfile, 'w').close()
    with open(auxfile, 'w') as f:
        for i in lines:
            f.write(i)
        

else:
    lines = None


# i = np.random.randint(0, 10, size=None, dtype=int)


if lines == None:
    print('done')
    open(auxfile, 'w').close()
    sys.exit()
# elif i == 2:
#     print('random int is 2')
#     open(auxfile, 'w').close()
#     print(lines)
#     sys.exit()
else:
    sys.stdout.flush()
    python = sys.executable
    os.execl(python,python,*sys.argv)