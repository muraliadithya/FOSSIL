# Lemma Synthesis

## Requirements

- [Python 3](https://www.python.org/downloads/)
- [CVC4 1.4](https://cvc4.github.io/downloads.html)

## Execution

- To run Python files: `python3 <filename>.py`
- To run CVC4 files using SyGuS: `cvc4 --lang=sygus2 <filename>.sy`
  - add option `--sygus-stream` to print outputs indefinitely
  - add option `--sygus-abort-size=<n>` with previous option to print outputs up to size `n`

## Worked out Example

- input: in Z3py format. see input-listlen.py
  - signature, rec defs, vc, default values for fcts
  - SyGuS grammar (given?)
- generate true models
  - old: use rank, see listlen-rank.py
  - new: evaluate recursive definitions manually, todo
- generate false model
  - see input-listlen-false.py
- take models and encode in SyGuS
  - loop through models output by Z3Py, convert to format readable by SyGuS
  - see input-listlen.py, listl-ex.sy
- generate constraints
  - in SyGuS
  - see listl-ex.sy
- check if lemma is provable and can prove vc
- unwanted lemmas
