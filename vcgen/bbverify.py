import argparse

from vcgen.interpreting_mod import vc

argparser = argparse.ArgumentParser('File containing code for basic block')
argparser.add_argument('bbfile')

args = argparser.parse_args()

with open(args.bbfile, 'r') as bb:
    bbcode = bb.read()

vc(bbcode.split('\n'))
