import os
import argparse
auxfile = 'vcgen/tests/aux.fsl'
os.makedirs(os.path.dirname(auxfile), exist_ok=True)
argparser = argparse.ArgumentParser('Check validity of a Hoare Triple using VC generation')
argparser.add_argument('--infile', help='.fsl File containing the Hoare Triple', default= 'vcgen/tests/mtest.fsl')

args = argparser.parse_args()
infile = args.infile
with open(infile, 'r') as f:
    lines = f.readlines()


open(auxfile, 'w').close()
with open(auxfile, 'w') as the_file:
    for i in lines:
        the_file.write(i)


