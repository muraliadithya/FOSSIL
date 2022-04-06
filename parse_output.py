import subprocess

with open('out_lvl0.log', 'w') as logfile:
    subprocess.call(['./test_all.sh'], stdout=logfile, stderr=logfile, shell=False)

with open('out_lvl1.log', 'w') as logfile:
    subprocess.call(['./test_lvl1.sh'], stdout=logfile, stderr=logfile, shell=False)

out_lvl0 = {}
with open('out_lvl0.log') as f:
    lvl0_lines = f.readlines()

out_lvl1 = {}
with open('out_lvl1.log') as f:
    lvl1_lines = f.readlines()

def parseLines(out_dict, lines):
    curr = ''
    time = -1
    lemmas = -1
    result = ''
    for line in lines:
        if 'Running' in line:
            idx = line.index('Running')
            curr = line[idx + len('Running '):][:-2]
        if 'so far' in line:
            idx = line.index('so far')
            lemmas = int(line[idx + len('so far: '):][:-1])
        if '|' in line:
            if 'FAILURE' in line:
                result = 'failure'
                idx = line.index('FAILURE')
                time = int(line[idx + len('FAILURE: '):][:-2])
            else:
                result = 'success'
                idx = line.index('SUCCESS')
                time = int(line[idx + len('SUCCESS: '):][:-2])
        if line == '\n':
            out_dict[curr] = (result, time, lemmas)

parseLines(out_lvl0, lvl0_lines)
parseLines(out_lvl1, lvl1_lines)

for benchmark in out_lvl0:
    result, time, lemmas = out_lvl0[benchmark]
    if result == 'success':
        print(benchmark + ': success -- ' + str(time) + 's, ' + str(lemmas) + ' lemmas proposed')
    else:
        if benchmark in out_lvl1:
            lvl1_result, lvl1_time, lvl1_lemmas = out_lvl1[benchmark]
            new_time = time + lvl1_time
            new_lemmas = lemmas + lvl1_lemmas
            if lvl1_result == 'success':
                print(benchmark + ': success -- ' + str(new_time) + 's, ' + str(new_lemmas) + ' lemmas proposed')
            else:
                print(benchmark + ': failure -- ' + str(new_time) + 's, ' + str(new_lemmas) + ' lemmas proposed')
        else:
            print(benchmark + ': failure -- ' + str(time) + 's, ' + str(lemmas) + ' lemmas proposed')
