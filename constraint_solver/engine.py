import sys
from lem_syn import *
import subprocess, itertools, warnings
import re, time

args = sys.argv[1:]
if args:
    filename = args[0]
    p = '-p' in args
    grammars, smt_file = replace_grammars(filename)
    start = time.time()
    proc = subprocess.Popen('cvc4 {} -m --lang=smt2'.format(smt_file), shell=True,
                            stdout=subprocess.PIPE, stderr=subprocess.PIPE, universal_newlines=True)
    cvc4_out, err = proc.communicate()
    if cvc4_out == '':
        if p:
            print(err)
    else:
        cvc4_lines = cvc4_out.split('\n')
        if cvc4_lines[0] == 'sat':
            model = {}
            for line in cvc4_lines:
                if 'define-fun' in line:
                    line = line.split(' ')
                    model[line[1]] = line[4][:-1] == 'true'
            for G in grammars:
                print(G.get_lemma(model=model, ind=False))
        else:
            print('unsat')
