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

def results_table(results, names, timeout=240):
    """
    Print LaTeX for table of FOSSIL experiment results.
    :param results: dictionary a triple of lemmas synthesized count, valid lemmas synthesized
        count, and runtime (value) for each benchmark (key)
    :param names: list of benchmark names
    :param timeout: float for special timeout symbol
    """
    for i,name in enumerate(names):
        if name not in results:
            print('ERROR',name)
            break
            
        # Organize and specialize data
        result = (
            replace(results[name][0], -1, '---'),
            replace(results[name][1], -1, '---'),
            replace(results[name][2], timeout, '\\bot'),
        )
        
        # Print data
        spacing = '\t'*(1 + int(len(name) < 16))
        print('\t\t' + '\t& '.join([name+spacing, *result]),'\\\\')
        
        # Split table
        if i == 2*len(names)//3 - 1:
            print('\t\t~ & ~ & ~ & ~ \\\\\n\n')
        elif i == len(names)//3:
            print('\n\n')
    return

def replace(s, value, replacement):
    if int(s) == value:
        return replacement
    else:
        return str(s)

def process_done(filename, timeout=900, name_terminate=True):
    """
    Process the text printed to terminal from FOSSIL experiments, such as in benchmark-suite/done.txt.
    :param filename: string
    :param timeout: float
    :param name_terminate: bool
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
                # Test runtime line
                line = line.split(' ')
                # Identify test
                try:
                    name = line[2].split('/')[1][:-3]
                except:
                    name = line[1].split('/')[1][:-3]
                p_index = name.find('.')
                if p_index != -1:
                    name = name[:p_index]
                
                # Locate outcome and runtimes
                if 'F' in line[3]:
                    # Failure case
                    runtime = -1.
                    lem_prop = -1
                    lem_prov = -1
                else:
                    # Success case
                    runtime = 0.
                    for word in line[4:]:
                        if 's' in word:
                            # Word with a runtime delimited by s for seconds 
                            runtime += float(word[:word.find('s')])
                    if 0 < runtime and runtime < 1:
                        runtime = 1
                    elif timeout < runtime:
                        runtime = timeout
                    runtime = int(runtime)
                    
                if name_terminate:
                    # Organize test results
                    if runtime == timeout:
                        pass
                    results[name] = (lem_prop, lem_prov, runtime)
                    names.append(name)
                    lem_prov = -1
            elif 'proposed' in line:
                # Lemmas proposed count line
                line = line.split(' ')
                if 'n/a' in line[-1]:
                    lem_prop = -1
                else:
                    lem_prop = int(line[-1][:-1])
                
                if not name_terminate:
                    # Organize test results
                    if runtime == timeout:
                        pass
                    results[name] = (lem_prop, lem_prov, runtime)
                    names.append(name)
                    lem_prov = -1
            elif 'proved' in line:
                # Lemmas proved count line
                line = line.split(' ')
                if 'n/a' in line[-1]:
                    lem_prov = -1
                else:
                    # Manual counting should agree with reported count
                    assert(lem_prov == int(line[-1][:-1]))
            elif 'VC' in line or 'Lemmas used to prove goal:' in line:
                lem_prov = 0
            elif lem_prov >= 0:
                if not line[0].isspace():
                    lem_prov += 1
    return names, results

def process_statements(filename, timeout=900, name_terminate=True):
    """
    Process the text printed to terminal from FOSSIL experiments, such as in benchmark-suite/done.txt.
    This generalizes process_done to incorporate derived lemma statements.
    :param filename: string
    :param timeout: float
    :param name_terminate: bool
    :return names: list
    :return results: dict
    """
    results = dict()
    names = []
    lem_prop = -1
    lem_prov = -1
    lemmas = []
    with open(filename, 'r') as output_file:
        for num,line in enumerate(output_file):
            if '|' in line:
                # Test runtime line
                line = line.split(' ')
                # Identify test
                try:
                    name = line[2].split('/')[1][:-3]
                except:
                    name = line[1].split('/')[1][:-3]
                p_index = name.find('.')
                if p_index != -1:
                    name = name[:p_index]
                
                # Locate outcome and runtimes
                if 'F' in line[3]:
                    # Failure case
                    runtime = -1.
                    lem_prop = -1
                    lem_prov = -1
                    lemmas = []
                else:
                    # Success case
                    runtime = 0.
                    for word in line[4:]:
                        if 's' in word:
                            # Word with a runtime delimited by s for seconds 
                            runtime += float(word[:word.find('s')])
                    if 0 < runtime and runtime < 1:
                        runtime = 1
                    elif timeout < runtime:
                        runtime = timeout
                    runtime = int(runtime)
                    
                if name_terminate:
                    # Organize test results
                    if runtime == timeout:
                        pass
                    results[name] = lemmas
                    names.append(name)
                    lem_prov = -1
                    lemmas = []
            elif 'proposed' in line:
                # Lemmas proposed count line
                line = line.split(' ')
                if 'n/a' in line[-1]:
                    lem_prop = -1
                else:
                    lem_prop = int(line[-1][:-1])
                
                if not name_terminate:
                    # Organize test results
                    if runtime == timeout:
                        pass
                    results[name] = lemmas
                    names.append(name)
                    lem_prov = -1
                    lemmas = []
            elif 'proved' in line:
                # Lemmas proved count line
                line = line.split(' ')
                if 'n/a' in line[-1]:
                    lem_prov = -1
                else:
                    # Manual counting should agree with reported count
                    assert(lem_prov == int(line[-1][:-1]))
            elif 'VC' in line or 'Lemmas used to prove goal:' in line:
                lem_prov = 0
            elif lem_prov >= 0:
                if not line[0].isspace():
                    lem_prov += 1
                    lemmas.append(line[:-1])
                else:
                    while line[0].isspace():
                        line = line[1:]
                    lemmas[-1] += ' ' + line[:-1]
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
        # How to best remove unnecessary parentheses? That is, around literals.
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