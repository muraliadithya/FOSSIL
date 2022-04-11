import numpy as np
import matplotlib as mpl
import matplotlib.pyplot as plt
plt.rcParams.update({'font.size': 14})
from matplotlib.lines import Line2D

def pretty_plot(x, y, x_name='FOSSIL[option]', y_name='FOSSIL', log=True, diagonal=True, square=True,
                measurement='runtime', unit='s', mark='o', bands=True, bands_curve=True, offset_band_label=False,
                tm_val=None, x_leg='lower right', y_leg='center right', z_leg='upper left', plotdir='./plots/'):
    """
    Display plot for batch of FOSSIL experiments. This is prepared to handle results which have been processed
    using the process_log or process_done function below, then normalized according to the adjust function below.
    Data for each axis is given in x and y, respectively. String names may be specified for axis/symbol labels.
    Logarithmic axis scale and diagonal reference line are toggles.
    Timeout legend placement is specified via *_leg strings for Matplotlib legends.
    Save directory may be specified; save file is determined by axis labels.
    :param x: array-like
    :param y: array-like
    :param x_name: string
    :param y_name: string
    :param log: bool
    :param diagonal: bool
    :param x_leg: string
    :param y_leg: string
    :param plotdir: string
    """
    # Build figure/axes
    fig = plt.figure()
    left, width = 0.1, 0.65
    bottom, height = 0.1, 0.65
    rect_scatter = [left, bottom, width, height]
    
    # Start with a rectangular Figure
    plt.figure(figsize=(8, 8))
    ax_scatter = plt.axes(rect_scatter)
    ax_scatter.tick_params(direction='in', top=True, right=True)

    # Prepare data
    data = np.vstack([np.array(x),
                      np.array(y)])

    # Generate masks
    if not tm_val:
        tm_val = np.max(data)
    timeout_x = np.array([xi>=tm_val for xi in data[0]])
    timeout_y = np.array([yi>=tm_val for yi in data[1]])
    no_timeout_ind = np.where(1-(timeout_x+timeout_y))[0]
    no_timeout = data[:,no_timeout_ind]
    
    # Derive the color data (distance from diagonal)
    colors = no_timeout[0] - no_timeout[1]
    c_max = np.max(colors)
    c_min = np.min(colors)
    colors = np.array([c/c_max + 0.3 if c > 0.
                       else -c/c_min - 0.2 if c < 0.
                       else 0 for c in colors])
    cmap = 'RdYlGn'

    # Plot the timeouts
    tm_factor = 1.05
    tm_x = np.where(timeout_x & ~timeout_y)
    x_t = np.exp(tm_factor*np.log(np.max(data[0])))*np.ones_like(tm_x[0])
    ax_scatter.scatter(x_t, data[1, tm_x],
                       color='green', marker='>', s=60)
    tm_y = np.where(timeout_y & ~timeout_x)
    y_t = np.exp(tm_factor*np.log(np.max(data[1])))*np.ones_like(tm_y[0])
    ax_scatter.scatter(data[0, tm_y], y_t,
                       color='maroon', marker='^', s=60)
    # Plot tests on which both tools timed out
    tm_z = np.where(timeout_x & timeout_y)
    z_t = np.exp(tm_factor*np.log(np.max(data)))*np.ones_like(tm_z[0])
    ax_scatter.scatter(z_t, z_t,
                       color='orange', marker='D', s=45)
    
    # Plot the data
    ax_scatter.scatter(no_timeout[0], no_timeout[1], marker=mark, s=(50 if mark=='o' else 30),
                       c=colors, cmap=cmap)
    
    # Fine-tune plot
    if log:
        if square:
            p_min = min(np.min(data), 0.9)
            p_max = np.exp(1.08*np.log(np.max(data)))
            ax_scatter.set_xlim(p_min, p_max)
            ax_scatter.set_ylim(p_min, p_max)
        else:
            ax_scatter.set_xlim((min(np.min(data[0]),0.9),np.exp(1.08*np.log(np.max(data[0])))))
            ax_scatter.set_ylim((min(np.min(data[1]),0.9),np.exp(1.08*np.log(np.max(data[1])))))
        ax_scatter.set_xscale('log')
        ax_scatter.set_yscale('log')
    else:
        if square:
            p_min = min(np.min(data), 0)
            p_max = 1.08*np.max(data)
            ax_scatter.set_xlim(p_min, p_max)
            ax_scatter.set_ylim(p_min, p_max)
        else:
            ax_scatter.set_xlim(min(np.min(data[0]), 0), 1.08*np.max(data[0]))
            ax_scatter.set_ylim(min(np.min(data[1]), 0), 1.08*np.max(data[1]))
    
    dd = np.linspace(min(np.min(data),0.9), np.max(data)+400, 10**3)
    if diagonal:
        ax_scatter.plot(dd, dd, '-', alpha=0.3, color='orange')
    if bands:
        if bands_curve:
            diff = 10
            dd_above = dd + diff
            dd_below = dd - diff
            ax_scatter.text(1, diff + 3, '+{}{}'.format(diff, unit if unit else ''), size=12)
            offset = int(offset_band_label) # Adjust for presence of timeout legend
            ax_scatter.text(diff + 2 + offset, 1 + offset, '-{}{}'.format(diff, unit if unit else ''), size=12)
        else:
            fact = 2
            dd_above = dd * 2
            dd_below = dd / 2
            ax_scatter.text(1.2, fact + 1, '{}x'.format(fact), size=12)
            ax_scatter.text(fact + 1, 1.3, '{:.1f}x'.format(1/fact), size=12)
        ax_scatter.plot(dd, dd_above, '-', alpha=0.3, color='orangered')
        ax_scatter.plot(dd, dd_below, '-', alpha=0.3, color='yellowgreen')

    # Manually set legends
    if len(tm_x[0]) > 0:
        legend_elements_x = [Line2D([0],[0], color='w', marker='>', 
                                   label='{}\ntimeout'.format(x_name),
                                   markerfacecolor='green', markersize=10)]
        legend_x = ax_scatter.legend(handles=legend_elements_x, loc=x_leg, prop={"size":12})
        ax_scatter.add_artist(legend_x)
    if len(tm_y[0]) > 0:
        legend_elements_y = [Line2D([0],[0], color='w', marker='^', 
                                   label='{}\ntimeout'.format(y_name),
                                   markerfacecolor='maroon', markersize=10)]
        legend_y = ax_scatter.legend(handles=legend_elements_y, loc=y_leg)
        ax_scatter.add_artist(legend_y)
    if len(tm_z[0]) > 0:
        legend_elements_z = [Line2D([0],[0], color='w', marker='D', 
                                   label='both timeout',
                                   markerfacecolor='orange', markersize=8)]
        legend_z = ax_scatter.legend(handles=legend_elements_z, loc=z_leg, fontsize=12)
        ax_scatter.add_artist(legend_z)

    # Set text
    ax_scatter.set_xlabel('{} {} {}'.format(x_name, measurement, '({})'.format(unit) if unit else ''))
    ax_scatter.set_ylabel('{} {} {}'.format(y_name, measurement, '({})'.format(unit) if unit else ''))
    fig.tight_layout()

    # Save and display plot
    savename = plotdir + '{}-{}_{}.png'.format(x_name, y_name, measurement).replace(' ','_').replace('[','_').replace(']','_')
    plt.savefig(savename, bbox_inches = 'tight', pad_inches = 0.2, dpi=100)
    plt.show()
    
def pretty_bar(x, y, x_name='FOSSIL[no Type-2]', y_name='FOSSIL', plotdir='./plots/'):
    """
    Display plot for batch of FOSSIL experiments. This is prepared to handle results which have been processed
    using the process_log or process_done function below, then normalized according to the adjust function below.
    Data for each axis is given in x and y, respectively.
    :param x: array-like
    :param y: array-like
    :param x_name: str
    :param y_name: str
    :param plotdir: str
    """
    fig = plt.figure()
    left, width = 0.1, 0.65
    bottom, height = 0.1, 0.65
    rect_bar = [left, bottom, width, height]
    plt.figure(figsize=(12, 6.32))
    ax = plt.axes(rect_bar)
    
    # Order data according to count on x axis in decreasing order
    y = [yi for _, yi in sorted(zip(x, y), reverse=True)]
    x = sorted(x, reverse=True)

    N = len(x)
    ind = np.arange(N)
    width = 0.35
    rects1 = ax.bar(ind, x, width, color='sandybrown')
    rects2 = ax.bar(ind+width, y, width, color='yellowgreen')

    ax.set_ylabel('Number of lemmas proposed')
    ax.set_xlabel('Benchmarks')
    ax.set_xticklabels([])
    ax.set_title('')
    ax.legend((rects1[0], rects2[0]), (x_name, y_name))
    fig.tight_layout()
    plt.savefig(plotdir + 'bar_FOSSIL_lemmas-proposed.png',
                bbox_inches='tight', pad_inches=0.2, dpi=100)
    plt.show()
    

def process_log(filename, timeout=240, old_format=False):
    """
    Process output logs from FOSSIL experiments with runtimes and lemma proposal counts.
    Example of format:
        >benchmark-suite/bst-left-right.py: failure -- 240s, 21 lemmas proposed
        >benchmark-suite/bst-left.py: success -- 57s, 9 lemmas proposed
    :param filename: str, name of file with experiment results
    :param timeout: float, timeout parameter used in run
    :param old_format: bool; if true, assume old format, as in process_done (lemmas not supported)
    :return names: list, names of detected tests
    :return results: dict, organized results containing tuple of runtime and
        lemma proposal count (value) for each test (key)
    """
    names = []
    results = dict()
    
    # Determine processing style for results line in format
    def process_old_line(line):
        if '|' not in line:
            return '', (-1, -1)
        # Assume each test result line has format:
        # >{n} | {filename} {SUCCESS/FAILURE}: {runtime}s
        line = line.split(' ')
        # Assume each filename has format "../test.py" with a single "/"
        name = line[2][line[2].find('/')+1:-3]
        runtime = int(line[4][:-2])
        if runtime > timeout:
            runtime = timeout
        proposals = -1
        return name, (runtime, proposals)
    def process_new_line(line):
        if not line:
            return '', (-1, -1)
        # Assume each line contains a test result, with format:
        # >{filename}: {success/failure} -- {runtime}s, {proposals} lemmas proposed
        line = line.split(' ')
        # Assume each filename has format "../test.py" with a single "/"
        name = line[0][line[0].find('/')+1:-4]
        runtime = int(line[3][:-2])
        if runtime > timeout:
            runtime = timeout
        proposals = int(line[4])
        return name, (runtime, proposals)
    if old_format:
        process_line = process_old_line
    else:
        process_line = process_new_line
         
    with open(filename, 'r') as f:
        # Iterate through log
        for line in f:
            name, (runtime, proposals) = process_line(line)
            if name:
                names.append(name)
                results[name] = (runtime, proposals)
    
    return names, results


def check_benchmark(first, second, first_name='true countermodels turned off',
                    second_name='true countermodels turned on', bench=10):
    X = 0
    Y = 0
    for i in range(len(first)):
        if first[i] > bench:
            X += 1
            if second[i] < first[i]:
                Y += 1
    if bench <= 0:
        print('Of the {} tests which ran with {},'.format(X, first_name))
    else:
        print('Of the {} tests which took more than {} seconds to run with {},'.format(X, bench, first_name))
    print('{} were faster with {}.'.format(Y, second_name))

    
def adjust(arr, mx=None, mn=1., log=True):
    """
    Normalize input data. This is intended to convert timeout data (set to -1) to above the current maximum
    (possibly across other datasets) for prettier plotting.
    :param arr: array-like
    :param mx: float
    :param mn: float
    :return: array
    """
    if mx is None or mx <= mn:
        if log:
            mx = np.exp(1.05*np.log(np.max(arr)))
        else:
            mx = 1.05*np.max(arr)
    return np.array([
        mx+1 if elt > mx else
        elt if 1 <= elt else
        mn if elt != -1 else
        mx+1 for elt in arr
    ])


def process_done(filename, timeout=900, name_terminate=True):
    """
    Process the text printed to terminal from FOSSIL experiments, such as in benchmark-suite/done.txt.
    These contain the particular lemmas proven as well as runtimes.
    :param filename: string
    :param timeout: float
    :param name_terminate: bool
    :return names: list
    :return results: dict
    """
    """
    Example of input file contents:
        Running benchmark-suite/bst-left-right.py:
        ---------------------------------------------------
        goal (no lemmas) is invalid
        lemma 1 is valid
        lemma 2 is valid
        goal (with lemmas) is valid
        goal is not first-order provable.
        Goal has been proven. Lemmas used to prove goal:
        Implies(bst(v1),
                Implies(hbst(v1)[v2], minr(v1) <= minr(v2)))
        Implies(bst(v1), Implies(hbst(v1)[v2], bst(v2)))
        Implies(bst(v1), Implies(hbst(v1)[v2], Not(v2 == nil)))
        Implies(bst(v1),
                Implies(hbst(v1)[v2], maxr(v2) <= maxr(v1)))
        Implies(bst(v1),
                Implies(minr(v1) <= maxr(v2), hbst(v2)[v2]))
        Implies(bst(v1),
                Implies(minr(v2) <= maxr(v1),
                        Implies(bst(v2), hbst(v2)[v2])))
        Total lemmas proposed: 28
        Total lemmas proved: 6
        1 | benchmark-suite/bst-left-right.py  SUCCESS: 180s
    """
    results = dict()
    names = []
    lem_prop = -1
    lem_val = -1
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
                    lem_val = -1
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
                    results[name] = (runtime, lem_prop, lem_val, lemmas)
                    names.append(name)
                    lem_val = -1.
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
                    results[name] = (runtime, lem_prop, lem_val, lemmas)
                    names.append(name)
                    lem_val = -1.
                    lemmas = []
            elif 'proved' in line:
                # Lemmas proved count line
                line = line.split(' ')
                if 'n/a' in line[-1]:
                    lem_val = -1
                else:
                    # Manual counting should agree with reported count
                    assert(lem_val == int(line[-1][:-1]))
            elif 'VC' in line or 'used to prove goal:' in line or 'unsat' in line:
                lem_val = 0
                lemmas = []
            elif lem_val >= 0:
                if not line[0].isspace():
                    lem_val += 1
                    lemmas.append(line)
                else:
                    lemmas[-1] += line
    return names, results

def process_VC(filename):
    """
    Process old VC table data.
    :param filename: string
    :return results: dict with keys 'lemmas', 'r0', 't0', 'r10', and 't10'
    """
    results = dict()
    names = []
    lem_prop = -1
    lem_val = -1
    with open(filename, 'r') as output_file:
        for num,line in enumerate(output_file):
            line = line.split('&')
            vc = int(line[0][:-1])
            try:
                rounds_0 = int(line[2][1:-1])
                time_0 = float(line[4].split(' ')[2])
            except:
                rounds_0 = -1
                time_0 = -1
            try:
                rounds_10 = int(line[3][1:-1])
                time_10 = float(line[5].split(' ')[2])
            except:
                rounds_10 = -1
                time_10 = -1
            results[vc] = {'lemmas': [int(name[1:]) for name in line[1][1:-1].split(', ')],
                           'r0': rounds_0,
                           't0': time_0,
                           'r10': rounds_10,
                           't10': time_10}
    return results