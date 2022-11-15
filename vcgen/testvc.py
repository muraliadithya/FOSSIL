import argparse
import importlib
from vcgen.parser import vc
import vcgen.parser
import sys
import os
argparser = argparse.ArgumentParser('Check validity of a Hoare Triple using VC generation')
# Making swaptwo.fsl a 'default' argument during development.
# Must make this a full menu with appropriate arguments before release.
argparser.add_argument('--infile', help='.fsl File containing the Hoare Triple', default='vcgen/tests/sll_append_iter/sll_append_iter_VC1.fsl')

args = argparser.parse_args()
infile = args.infile
with open(infile, 'r') as f:
    lines = f.readlines()

vc(lines)