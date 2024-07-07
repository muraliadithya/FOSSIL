import argparse
import time
import os
import subprocess

import logging
from BBGenerator import BBGenerator

# # os.makedirs(os.path.dirname(logfile), exist_ok=True)
# logfile  ='C:\\Users\\hrish\\OneDrive\\Documents\\GitHub\\FOSSIL\\vcgen\\logs\\vcgen.txt'

# # logfile = '\\logs\\vcgen.txt'

# logging.basicConfig(filename=logfile, level=logging.INFO)
# with open(logfile, 'a+'):
#     pass

argparser = argparse.ArgumentParser()
argparser.add_argument('program')
argparser.add_argument('--lang', choices=['sl', 'fl'], default='sl', help='Language of annotations (SL or FL)')
argparser.add_argument('--mode', type=int, choices=[0, 1, 2, 3, 4, 5], default=4, help='[EXPERTS ONLY] Solver mode for reasoning with VCs')
argparser.add_argument('--one-vc', dest='one_vc', action='store_true', help='[EXPERTS ONLY] Solving option to process all VCs including side conditions with one SMT call')
argparser.add_argument('--weaken-alloc-check', type=int, choices=[0,1,2], default=0, help='[EXPERTS ONLY] Removes restrictions for tightness of heap')
args = argparser.parse_args()

curr_path = os.path.abspath('.')
tmp_folder = os.path.join(curr_path, 'tmp')

if os.path.isfile(args.program):
    if str(args.program).endswith('.fsl'):
        progfiles = [args.program]
    else:
        raise Exception('First argument must be either a .fsl file or a folder with .fsl files')
else:
    progfiles = [os.path.join(args.program,pf) for pf in os.listdir(args.program) if pf.endswith('.fsl') and os.path.isfile(os.path.join(args.program,pf))]

times = []

for prog in progfiles:
    # logging.info(prog + '\n')
    print('****************************************************************************************')
    progname = os.path.basename(prog).split('.fsl')[0]
    prog_folder = os.path.join(tmp_folder, progname)
    os.makedirs(prog_folder, exist_ok=True)

    with open(prog, 'r') as f:
        progtext = f.read()


    start = time.time()

    bbgen_object = BBGenerator()
    parsed_bbs = bbgen_object.parse_input(progtext)

    for i, parsed_bb in enumerate(parsed_bbs):
        with open(os.path.join(prog_folder,f'bb{str(i+1)}.fsl'), 'w') as f:
            f.write('\n'.join(parsed_bb))

    # Run each bb
    for i in range(len(parsed_bbs)):
        bb_file = os.path.join(prog_folder,f'bb{str(i+1)}.fsl')
        callargs = ['python', 'runbb.py', f'{bb_file}', f'--lang={args.lang}', f'--mode={args.mode}', f'--weaken-alloc-check={args.weaken_alloc_check}']
        if args.one_vc:
            callargs += ['--one-vc']
        subprocess.run(callargs)
    # logging.info('--------------' + '\n')

    end = time.time()
    time_taken = end-start
    print(f'Time: {time_taken}')
    times.append((progname, time_taken))

for i in times:
    print(i)
