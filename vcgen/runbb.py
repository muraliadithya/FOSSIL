from interpreting_vcalt import vc  
import argparse

argparser = argparse.ArgumentParser()
argparser.add_argument('bbfile')
argparser.add_argument('mode')

args = argparser.parse_args()

with open(args.bbfile, 'r') as f:
    bbtext = f.read()

vc(bbtext.split('\n'), int(args.mode))

