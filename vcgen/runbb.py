from interpreting_vcalt import vc  
import argparse

argparser = argparse.ArgumentParser()
argparser.add_argument('bbfile')
argparser.add_argument('--lang', choices=['sl', 'fl'], default='sl', help='Language of annotations (SL or FL)')
argparser.add_argument('--mode', type=int, choices=[0, 1, 2], default= 0, help='[EXPERTS ONLY] Solver mode for reasoning with VCs')
argparser.add_argument('--one-vc', dest='one_vc', action='store_true', help='[EXPERTS ONLY] Solving option to process all VCs including side conditions with one SMT call')
argparser.add_argument('--weaken-alloc-check', type=int, choices=[0,1,2], default=0, help='[EXPERTS ONLY] Removes restrictions for tightness of heap')


args = argparser.parse_args()

with open(args.bbfile, 'r') as f:
    bbtext = f.read()

vc(bbtext.split('\n'), args.mode, args.lang, not args.one_vc, args.weaken_alloc_check)

