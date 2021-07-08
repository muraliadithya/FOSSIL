import numpy as np


LATEX_REP = {
    '\\n': ' \\\\ & ', # very case-dependent
    '_': '\\textunderscore ',
    '<=': '$\\leq$',
    '==': '$=$',
    '!=': '$\\neq$',
    'Not': '$\\neg$',
    '/\\': '$\\wedge$',
    '\\/': '$\\vee$',
    '=>': '$\\Rightarrow$',
    '\\in': '$\\in$',
}
LATEX_PRO = {
    'Implies': '$\\Rightarrow$',
    'Or': '$\\vee$',
    'And': '$\\wedge$',
}

def process_done(filename):
    """
    Process the text printed to terminal from FOSSIL experiments, such as in benchmark-suite/done.txt.
    :param filename: string
    :return names: list
    :return results: dict
    """
    results = dict()
    names = []
    lem_prop = -1
    lem_prov = -1
    with open(filename, 'r') as output_file:
        for num,line in enumerate(output_file):
            if '|' in line:
                line = line.split(' ')
                try:
                    name = line[2].split('/')[1][:-3]
                except:
                    name = line[1].split('/')[1][:-3]
                p_index = name.find('.')
                if p_index != -1:
                    name = name[:p_index]
                s_index = line[-1].find('s')
                runtime = line[-1][:s_index]
                if runtime[0] == 'F':
                    runtime = -1.
                    lem_prop = -1
                    lem_prov = -1
                else:
                    runtime = float(runtime)
                    if 0. < runtime and runtime < 1.:
                        runtime = 1.
                    runtime = str(int(runtime)) + 's'
                results[name] = (lem_prop, lem_prov, runtime)
                names.append(name)
                lem_prov = -1
            elif 'Total lemmas proposed' in line:
                line = line.split(' ')
                lem_prop = int(line[-1][:-1])
            elif 'VC' in line or 'Lemmas used to prove goal:' in line:
                lem_prov = 0
            elif lem_prov >= 0:
                if not line[0].isspace():
                    lem_prov += 1
    return names, results

def process_statements(filename):
    """
    Process the text printed to terminal from FOSSIL experiments, such as in benchmark-suite/done.txt.
    This generalizes process_done to incorporate derived lemma statements.
    :param filename: string
    :return names: list
    :return results: dict
    """
    results = dict()
    names = []
    lem_prop = -1
    lem_prov = -1
    with open(filename, 'r') as output_file:
        for num,line in enumerate(output_file):
            if '|' in line:
                line = line.split(' ')
                try:
                    name = line[2].split('/')[1][:-3]
                except:
                    name = line[1].split('/')[1][:-3]
                p_index = name.find('.')
                if p_index != -1:
                    name = name[:p_index]
                s_index = line[-1].find('s')
                runtime = line[-1][:s_index]
                if runtime[0] == 'F':
                    runtime = -1.
                    lem_prop = -1
                    lem_prov = -1
                    lemmas = []
                else:
                    runtime = float(runtime)
                    if 0. < runtime and runtime < 1.:
                        runtime = 1.
                    runtime = str(int(runtime)) + 's'
                results[name] = lemmas
                names.append(name)
                lem_prov = -1
            elif 'Total lemmas proposed' in line:
                line = line.split(' ')
                lem_prop = int(line[-1][:-1])
            elif 'VC' in line or 'Lemmas used to prove goal:' in line:
                lem_prov = 0
                lemmas = []
            elif lem_prov >= 0:
                if not line[0].isspace():
                    lem_prov += 1
                    lemmas.append(line[:-1])
                else:
                    while line[0].isspace():
                        line = line[1:]
                    lemmas[-1] += ' '+line[:-1]
    return names, results

def parse_latex(line):
    """
    Parse logical formulas into LaTeX.
    :param line: string
    :return line: string
    """
    for kw in LATEX_PRO:
        line = _parse(line, kw)
    for kw in LATEX_REP:
        line = line.replace(kw, LATEX_REP[kw])
    return line

def _parse(line, kw):
    """
    Auxiliary function to parse_latex.
    """
    if kw in line:
        index = line.find(kw)+len(kw)+1
        depth = 0
        comma = False
        arg1 = line[index]
        while not comma:
            index += 1
            c = line[index]
            arg1 += c
            if c == '(':
                depth += 1
            elif c == ')':
                depth -= 1
            elif c == ',' and depth == 0:
                comma = True
        arg1 = arg1[:-1]
        parenth = False
        index += 1
        index += int(line[index].isspace())
        arg2 = line[index]
        while not parenth:
            index += 1
            c = line[index]
            arg2 += c
            if c == '(':
                depth += 1
            elif c == ')':
                if depth == 0:
                    parenth = True
                else:
                    depth -= 1
        arg2 = arg2[:-1]
        return '(' + _parse(arg1,kw) + ') ' + LATEX_PRO[kw] + ' (' + _parse(arg2,kw) + ')'
    else:
        return line

def get_order(filename):
    """
    Process a simple text file giving order to theorem names.
    :param filename: string
    :return ordered_names: list
    """
    ordered_names = []
    with open(filename, 'r') as file:
        for num,line in enumerate(file):
            ordered_names.append(line[:-1])
    return ordered_names