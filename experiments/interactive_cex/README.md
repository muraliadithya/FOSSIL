This directory contains JSON files containing one counterexample model each.  
Each model is of the following form:

```buildoutcfg
{
"universe": list of int,
"func_or_const_name": value,
"func_or_const_name": value,
...,
<Optional entries>
"assert": list of assertions,
"assertfailure": list of failures
}
```

where `universe` must be mapped to a list of integers dnoting the foreground universe
and `func_or_const_name` is the name of a constant, function, or relation symbol 
in your vocabulary. The values for the symbols must follow this convention:

```buildoutcfg
constant symbol : valuation of constant
function symbol g of arity k : list of k+1-sized-lists for g
k+1-sized-list for g: list of k+1 values a1, a2,...ak, b such that g(a1,...ak) = b 
```

The individual values themselves are written according to their type:

```buildoutcfg
int: integer (plain integers are JSON-compatible)
bool: true/false (JSON-compatible)
set of ints: list of ints
```

No other types are supported.

Refer to the files in this directory for examples of counterexample models 
written in the above format (JSON editor recommended for viewing). The models 
in those files are counterexamples provided 
for the benchmark in `../../done/lseg-nil-list.py`
Refer to the indicated file for the code stub that allows the usage of 
these counterexamples.  
To see the counterexamples in action temporarily rename one or both of the 
files to a .txt extension and run the benchmark. 

Here is the output without either file:
```
goal is not first-order provable.
goal cannot be proved using induction.
proposed lemma: Implies(lseg(v1, v2), lseg(nil, v1))
total lemmas so far: 1
proposed lemma cannot be proved.
You are in the interactive mode. Please add a counterexample.
If you want to mix automatically generated counterexamples, set option use_cex_models.
```

This is the output after adding `cex1.json` which contains a counterexample 
to `\forall v1, v2. lseg(v1, v2) => lseg(nil, v2)`:
```
goal is not first-order provable.
goal cannot be proved using induction.
proposed lemma: Implies(lseg(v1, v2), lst(v1))
total lemmas so far: 1
proposed lemma cannot be proved.
You are in the interactive mode. Please add a counterexample.
If you want to mix automatically generated counterexamples, set option use_cex_models.
```

Similarly setting the option for automatically generated counterexamples (options.use_cex_models) 
shows that adding both files reduces the number of rounds of lemma proposal.  

IMPORTANT NOTES:
- Every model must be in its own file.
- Every symbol must be interpreted, but the interpretation need not be total. The tool 
can handle partial but not empty interpretations.
  
EXTRAS:

The JSON string can have an extra entry `assert` or `assertfailure` containing a list 
of list of assertions. Each assertion is written in the form 
`[var1, var2, ... vark, assertion]` where `var1, var2, ...vark` are the names of 
universally quantified variables and `assertion` is a string written in SMT-Lib format. 
The vocabulary of the assertion is given by the constant function symbols as defined 
above.  
- Entries under `assert` are expected to hold on the finite model
- Entries under `assertfailure` are expected to fail on the finite model
The files in this directory have examples of the `assertfailure` field.