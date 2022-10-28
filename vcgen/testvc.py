
import vcgen.myparser
from vcgen.myparser import vc


with open(r'C:\Users\hrish\OneDrive\Documents\GitHub\FOSSIL\vcgen\swaptwo.txt') as f:
    lines= f.readlines()

vc(lines)