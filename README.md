# lemma-synthesis

worked out example of what we give to all these tools:
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
