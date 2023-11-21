import argparse
import time
import os
import subprocess

from BBGenerator import BBGenerator


argparser = argparse.ArgumentParser()
argparser.add_argument('program')


argparser.add_argument('mode')


args = argparser.parse_args()

curr_path = os.path.abspath('.')
tmp_folder = os.path.join(curr_path, 'tmp')

progfiles = [os.path.join(args.program,pf) for pf in os.listdir(args.program) if pf.endswith('.fsl') and os.path.isfile(os.path.join(args.program,pf))]

times = []

for prog in progfiles:
    print('****************************************************************************************')
    progname = os.path.basename(prog).split('.fsl')[0]
    prog_folder = os.path.join(tmp_folder, progname)
    os.makedirs(prog_folder,exist_ok=True)

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
        subprocess.run(['python','runbb.py', f'{bb_file}', args.mode])

    end = time.time()
    time_taken = end-start
    print(f'Time: {time_taken}')
    times.append((progname, time_taken))

for i in times:
    print(i)
