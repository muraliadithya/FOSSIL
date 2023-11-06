from interpreting_vcalt import vc  
import argparse

argparser = argparse.ArgumentParser()
argparser.add_argument('bbfile')

args = argparser.parse_args()

with open(args.bbfile, 'r') as f:
    bbtext = f.read()

vc(bbtext.split('\n'))

