# Lemma Synthesis

## Requirements

- [Python 3](https://www.python.org/downloads/)
- [CVC4 1.4](https://cvc4.github.io/downloads.html)

## Execution

- To run Python files: `python3 <filename>.py`
- To run CVC4 files directly using SyGuS: `cvc4 --lang=sygus2 <filename>.sy`
  - add option `--sygus-stream` to print outputs indefinitely
  - add option `--sygus-abort-size=<n>` with previous option to print outputs up to size `n`

## Worked out Example

- input: in Z3py format. see dlist-list.py
  - signature, rec defs, vc, default values for fcts
  - SyGuS grammar
- generate true models
  - evaluate recursive definitions manually, see true_models.py
  - can limit number of true models used as parameter
- generate false model
  - see false_models.py
  - if no false model exists, the VC has been proven with the lemmas generated
- take models and encode in SyGuS
  - loop through models output by Z3Py, convert to format readable by SyGuS
  - see lemma-synthesis.py
- generate SyGuS constraints
  - see lemma-synthesis.py
- run generated SyGuS file to output stream of lemmas (up to size n)
  - see lemma-synthesis.py
- for each lemma generated:
  - convert lemma from smtlib format to z3Py format, see lemsynth_utils.py
  - disregard lemma if it had been previously generated
  - check if lemma is provable using natural proofs + induction principle, see false_models.py
  - if so, add lemma to axioms to be instantiated
  - if not, add lemma to list of lemmas that had been generaated
  - see dlist-list.py
