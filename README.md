# FL/SL-FL Verification Condition Generator

A tool for generating and proving verification conditions for heap manipulation programs annotated
with Frame Logic (FL) or FL inspired Separation Logic (SL-FL) specification.

TODO: [cite paper here]

---

## Table of Contents

0. [Requirements](#requirements)
1. [Installation](#installation)
2. [Experiments](#experiments)
3. [How to write benchmarks](#how-to-write-benchmarks)

---

## Requirements
- [Python 3.5 or above](https://www.python.org/downloads/)
- [Z3Py](https://pypi.org/project/z3-solver/)
- [CVC4 1.9](https://cvc4.github.io/downloads.html) <!-- Check if we use this>


## Installation

1. Clone or download the repo.
2. Install Z3Py.
3. Install the naturalproof package from the FOSSIL repository.
    - Add the path to the naturalproofs toplevel folder to `PYTHONPATH`: execute `export PYTHONPATH ="/path/to/naturalproofs":$PYTHONPATH` or add it to `~/.bashrc` and then do `source ~/.bashrc`.
4. Change directory to `vcgen`.

## Experiments

- Benchmarks written with SL-FL (resp. FL) are in the directory `benchmarksSL` (resp. `verifiedEqSP`). This contains subdirectories categorized by the primary data structure being manipulated, as well an `all` directory containing all the benchmarks.

- To run all the SL-FL benchmarks, run `python runbench.py ./benchmarksSL/all/`
    - NOTE: `runbench.py` runs a python script of the form `python ...`. You may need add a symbolic link `python` if your system does not recognize the `python` command. You may also replace the command in `runbench.py` (line 61) with the appropriate one. 
- To run all the FL benchmarks, run `python runbench.py ./benchmarksFL/all/ --lang fl`
    - NOTE: The tool assumes specifications are in SL-FL by default. Use `--lang fl` when running FL annotated files.
- To run individual files, simply run `python runbench.py ./path-to-file/filename.fsl`
- Additionally, you may log the entire output of the tool by adding `&> name-of-log-file.txt`.

- The tool generates multiples VCs per file. 
    - It prints 'goal is valid' for each VC it is able to prove the VC valid, and 'goal not proven' otherwise.
    - For each file, it prints the total execution time.


## How to write benchmarks

### Structure of a File

Each benchmark file contains variable declarations, followed by function declarations (both pointers as well as recursively defined functions), then provides definitions for recursive functions, defines certain inductive lemmas which are checked automatically, and finally the methods. These are written in a lisp-like format.

A simple SLFL program to help read the benchmarks:

> (Var x Loc)                           /* variable x of location sort.*/
> (Var ret Loc)
>
> (Function next Loc Loc)               /* pointer next:Loc --> Loc */
> (Function keys Loc Int)
>
> (EqSp (List (Keys)))                  /* Declare that the recursive functions
                                            List and Keys (which must be declared afterwards) have the same heaplet (support). */
>
> (RecFunction List Loc Bool)           /* Recursive function List:Loc --> Bool. */
> (RecFunction Keys Loc SetInt)
>
> (RecDef (List x) (ite (= x nil) True 
>                            (Exists (= y (next x)) (* (= (next x) (next x)) (List y))))) 
>                             /* The definition of the recursive function List. RecFunctions must be declasred before providing a definition. */
> (RecDef (Keys x) (ite (= x nil) EmptySetInt  
>                            (SetAdd (Keys (next x)) (key x))))
>
>  (Program example (x) (ret))             
>  (Pre (List x))                                       /* Preconditin:   (List x) holds at the start of the program */
>  (Post (= (Keys ret) (SetAdd (Old (Keys x)) k)))      /* Postcondition: (Keys ret) at the end of the program is the same as (Keys x) at the start
                                                        along with k.*/
>  (alloc ret)                           /* Allocate a new location named ret. */
>  (assume (not (= ret nil)))
>  (assign (key ret) k)                 
>  (assign (next ret) x)                /* Mutation: the next pointer of ret points to x. */
>  (return)                             /* end of program. */


The corresponding FL annotations for the program above:
> (RecDef (List x) (ite (= x nil) True (and (List (next x)) (not (IsMember x (Sp (List (antiSp (next x))))))))) 
>                             /* 'Sp' is the support operator, and 'antiSp' is the cloud operator. */
> (RecDef (Keys x) (ite (= x nil) EmptySetInt
>                       (SetAdd (Keys (next x)) (key x))))
> (Pre (List x)) 
> (Post (= (Keys ret) (SetAdd (Old (Keys x)) k)))

#### Writing Benchmarks

A program should be written in the following format:

[Variables]$$^{*}$$.

[Pointers]$$^{*}$$.

([Equal-Supports] | $$\epsilon$$).

[RecursiveFunctionNames]$$^{*}$$.

[RecursiveFunctionDefinitions]$$^{*}$$.

[Lemmas]$$^{*}$$.

[Methods]$$^{*}$$.

NOTE: Variables may be declared anytime before [Methods].


[Variables]                    - (Var var-name sort)
                                  /* NOTE: The allowed sortsare: `Loc`, `Int`, `Bool`, `SetLoc`, `SetInt`, `SetBool` */

[Pointers]                     - (Function func Loc sort)

[Equal-Supports]               - (EqSp (recfunc1 (recfunc11 recfunc12 ...)) (recfunc2 (recfunc21 recfunct22) ...) ...) 

[RecursiveFunctionNames]       - (RecFunction recfunc input-sort1 input-sort2 ... output-sort) 
                                 /* where input-sort1, input-sort2... must be `Loc`. output-sort can by anything*/

[RecursiveFunctionDefintions]  - (RecDef (recfunc arg1 arg2 ...) [logic-formula])
                                 /* where relation symbols occur positively in the [logic-formula],
                                    (or inside a support expression for frame logic formulas). */

[Lemmas]                       - (lemma (arg1 arg2 ...) (=> (recfunc ..args..) [fl-formula] ))
                                  /* NOTE: Lemmas are currently written in FL (even for SL benchmarks).*/

[Methods]                      - (Program method-name (..input-args..) (..output-vars..))
                                 (Pre [logic-formula])
                                 (Post [logic-formula-with-old])
                                 [Program]

[Program]                      - (assign var1 var2) | (assign var1 (func var2)) | (assign (func var1) var2)
                                 |(assign bg-var bg-term) 
                                 | (alloc var1) | (free var1) | (call method-name (..input-vars..) (..output-vars..))
                                 | (assume deref-free-formula)
                                 | (return)
                                 | (If (deref-free-formula)
                                      Then [Program]
                                      Else [Program]
                                    )
                                 | [Program] [Program]
                                 /* where
                                    - bg-terms are those of a background sort. Eg: `(assign m (+ (IntSort 1) n))` assigns 1 + n to the variable m.  
                                    - deref-free-fromulas are those whose support is empty. 
                                    - method-name can be any method defined before (and including) the current one.
                                    */
        

[logic-formula]                 -  Either [sl-formula] or [fl-formula] depending on the benchmark.

###### SLFL-Formulas
[sl-formula]                    -  True | False | (= var1 var2) | (not (= var1 var2)) | (= var1 nil) | (not (= var1 nil)) | (= var1 (func1 var2))
                                  | [set-formula]
                                  | [int-formula] 
                                  | (* [sl-formula] [sl-formula]) | (and [sl-formula] [sl-formula]) |  (nonsepand [sl-formula] [sl-formula])
                                  | (or [sl-formula] [sl-formula]) | (ite [sl-formula] [sl-formula] [sl-formula]) 
                                  | (Exists (= var1 (func1 var2)) [sl-formula]) | (boolean-recfunc ..vars..)   

[set-formula]                   - [locset-formula] | [boolset-formula] | [intset-formula]

[locset-formula]                - (= [locset-term] [locset-term]) | (IsMember var1 [locset-term]) | (IsSubset [locset-term] [locset-term]) 
                                  | (Not [locset-formula])

[locset-term]                   - EmptySetLoc | (locset-recfunc ..vars..) 
                                  |(SetAdd [locset-term] var1) | (SetDel [locset-term] var1) | (SetIntersect [locset-term] [locset-term])
                                  | (SetUnion [locset-term] [locset-term]) | | (ite [sl-formula] [locset-term] [locset-term])

/* NOTE: [set-formula] and [set-term] above are defined for sets of `Loc`s. They can also be defined for `Bool`, `Int` with variables, recursive-functions of the appropriate sorts, and whose corresponding empty sets are `EmptySetBool` and `EmptySetInt`.*/ 


[int-formula]                   - (< [int-term] [int-term]) | (> [int-term] [int-term]) | (<= [int-term] [int-term]) | (>= [int-term] [int-term])
                                  | (= [int-term] [int-term]) | (not [int-formula])

[int-term]                      - (IntConst [int]) | (intfunc locvar)| intvar | (+ [int-term] [int-term]) | (- [int-term] [int-term])


 
> A singly linked list can be defined as follows: 
>                       (RecDef (List x) (ite (= x nil) True (Exists (= y (next x)) (* (= (next x) (next x)) (List y)))))
> The lists List(x) and List(y) are disjoint: 
                        (* (List x) (List y))

###### FL-formulas
FL formulas are written similarly. [TODO: cite paper here.]

- (Sp ...) is used for the support operator.
- (antiSp ...) is used for cloud operator.

> A singly linked list can be defined as follows: 
>                       (RecDef (List x) (ite (= x nil) True (and (List (next x)) (not (IsMember x (Sp (List (antiSp (next x)))))))))
> The lists List(x) and List(y) are disjoint: 
>                       (and (List x) (List y) (= EmptySetLoc (SetIntersect (Sp (List x)) (Sp (List y)))) )


###### `Old` operator
When writing postconditions, one may write (Old (recdef ..vars..)) to refer to the recdef as defined at the beginning of the program.

>  (Program example (x) (ret))
>  (Pre (List x))                               
>  (Post (= (Keys ret) (SetAdd (Old (Keys x)) k)))
>  (alloc ret)
>  (assume (not (= ret nil)))
>  (assign (key ret) k)
>  (assign (next ret) x)
>  (return)

