import argparse
import os

from vcgen.BBGenerator import BBGenerator


argparser = argparse.ArgumentParser()
argparser.add_argument('progfile', help='Path to .fsl file containing the program to be verified')

args = argparser.parse_args()
progfile = args.progfile
with open(progfile, 'r') as f:
    program = f.read()
progname = os.path.basename(progfile).split('.fsl')[0]

bbparser = BBGenerator()
parsed_bbs = bbparser.parse_input(program)

print(f'Number of basic blocks: {len(parsed_bbs)}')

bbpath = os.path.join(os.path.abspath('.'), '.tmp', progname)
os.makedirs(bbpath, exist_ok=True)

for i, bb in enumerate(parsed_bbs):
    bbfile = os.path.join(bbpath, f'bb_{str(i+1)}.fsl')
    with open(bbfile, 'w') as f:
        f.write('\n'.join(parsed_bbs[i]))

print(f'Basic blocks written to .tmp/{progname}/bb_#.fsl')
