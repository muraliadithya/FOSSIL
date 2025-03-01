### Declaring the Heaplet of two Recursive definitions as Equal

The user may declare the heap of two recursive functions to be the same (see Sec. 6.2.3 of the paper). For instance, the set of locations upon which computing Keys(x) and List(x) depends on are the same.

This declaration is made using the `EqSp` command. For example, (EqSp (List (Keys))) declares that the support of Keys is the same as that of List, and only generates one (common) support defintion.

The tool does not automatically verify this, and it is up to the user to ensure only the correct recursive functions are equated.
Such statements can be proven seperately using the tool by writing them as inductive lemmas. For example, we may prove the support of List(x) and Key(x) by writing the program:

(Program temp (x) (ret))
(Pre (ite (= x nil) True (= (Sp (List (antiSp (next x)))) (Sp (Keys (antiSp (next x)))))))
(Post (= (Sp (List x)) (Sp (Keys x))))
(return)

Note that the above is *not* a heap program, but simply a programmatic way of writing a *lemma*, and does not require the heap tightness condition. We may tell the tool to elide the heap condition check with the command `--weaken-alloc 2`. See `./EqSpProofs/lemmaseqspFL/sl_eqsp.fsl` for the full file.

The proofs for all the EqSps used in the benchmarks are written in `./EqSpProofs/lemmaseqspFL/` and `./EqSpProofs/lemmaseqspSL/`. To run these proofs,
- For SLFL: `python runbench.py ./EqSpProofs/lemmaseqspSL/ --weaken-alloc 2` 
- For FL: `python runbench.py ./EqSpProofs/lemmaseqspFL/ --lang fl --weaken-alloc 2`  





