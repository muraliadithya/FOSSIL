# FL/SL-FL Verification Condition Generator

A tool for generating and proving verification conditions for heap manipulation programs annotated
with Frame Logic (FL) or FL inspired Separation Logic (SL-FL) specification. [cite paper]

---

## Table of Contents

0. [Requirements](#requirements)
1. [Installation](#installation)
2. [Experiments](#experiments)
3. [Structure of a File](#structureofafile)

---

## Requirements
- [Python 3.5 or above](https://www.python.org/downloads/)
- [Z3Py](https://pypi.org/project/z3-solver/)


## Installation

1. Clone or download the repo.
2. Install Z3Py.
3. Add the path to the naturalproof subdirectory to PYTHONPATH - execute `export PYTHONPATH="/path/to/naturalproofs":$PYTHONPATH` or add it to `~/.bashrc` and then do `source ~/.bashrc`.
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



## Structure of a file

Programs are written in `.fsl` files. Each benchmark file contains variable declarations, followed by function declarations (both pointers as well as recursively defined functions), then provides definitions for recursive functions, defines certain inductive lemmas which are checked automatically, and finally the methods. These are written in a lisp-like format.

A simple SLFL program to help read the benchmarks:

> (Var x Loc) <br>
> (Var ret Loc) <br>
> (Var k Int)

Declares variable x, ret of location sort.

> (Function next Loc Loc) <br>
> (Function key Loc Int)

Declare pointer next:Loc --> Loc and data field key:Loc --> Int.

> (EqSp (List (Keys)))

Declare that the recursive functions List and Keys have the same heaplet (support).

> (RecFunction List Loc Bool) <br>
> (RecFunction Keys Loc SetInt)

Recursive function List:Loc --> Bool and Keys:Loc -> SetInt.

> (RecDef (List x) (ite (= x nil) True (Exists (= y (next x)) (\* (= (next x) (next x)) (List y))))) <br>
> (RecDef (Keys x) (ite (= x nil) EmptySetInt (SetAdd (Keys (next x)) (key x))))

The definition of List and Keys. RecFunctions must be declared before providing a definition.

>  (Program example (x) (ret)) <br>
>  (Pre (List x))

Precondition: (List x) holds at the start of the program.
>  (Post (= (Keys ret) (SetAdd (Old (Keys x)) k)))

 Postcondition: (Keys ret) at the end of the program is the same as (Keys x) and k .
>  (alloc ret)                         

Allocate a new location named ret.
>  (assume (not (= ret nil))) <br>
>  (assign (key ret) k) <br>
>  (assign (next ret) x)  

Mutation: the next pointer of ret points to x.
>  (return)                            

 end of program.



#### Writing Benchmarks

A program should be written in the following format:

[Variables]\* \
[MutableFuncs]\* \
([Equal-Supports] | $\epsilon$) \
[RecursiveFunctionNames]\* \
[RecursiveFunctionDefinitions]\* \
[Lemmas]\* \
[Methods]\* 

NOTE: Variables may be declared anytime before [Methods].




> [Variables]                    := (Var var-name sort) \
\> The allowed sorts are `Loc`, `Int`, `Bool`, `SetLoc`, `SetInt` `SetBool`

> [MutableFuncs]                   := (Function func Loc sort)

> [Equal-Supports]               := (EqSp (recfunc1 (recfunc11 recfunc12 ...)) (recfunc2 (recfunc21 recfunct22) ...) ...) 

> [RecursiveFunctionNames]       := (RecFunction recfunc input-sort1 input-sort2 ... output-sort)  
\> where input-sort1, input-sort2... must be `Loc`. output-sort can by anything

> [RecursiveFunctionDefintions]  := (RecDef (recfunc arg1 arg2 ...) [logic-formula]) \
\> where relation symbols occur positively in the [logic-formula], (or inside a support expression for frame logic formulas).

> [Lemmas]                       := (lemma (arg1 arg2 ...) (=> (recfunc ..args..) [fl-formula] )) \
\> NOTE: Lemmas are currently written in FL (even for SL benchmarks).

> [Methods]                      := (Program method-name (..input-args..) (..output-vars..)) \
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;(Pre [logic-formula]) \
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;(Post [logic-formula-with-old]) \
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;[Program]

> [Program]                      := 
> (assign var1 var2) <br> 
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (assign var1 (func var2)) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (assign (func var1) var2)  <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (assign bg-var bg-term) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;|  (alloc var1) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (free var1) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (call method-name (..input-vars..) (..output-vars..)) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;|  (assume deref-free-formula) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;|  (return) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (If (deref-free-formula) Then [Program] Else [Program]) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| [Program] [Program] <br> <br>
> \> where: `bg-terms` are those of a background sort. Eg: `(assign m (+ (IntSort 1) n))` assigns 1 + n to the variable m; deref-free-fromulas are those whose support is empty; method-name can be any method defined before (and including) the current one; [logic-formula] is either an `SLFL-formula` or an `FL-formula` depending on the benchmark; [logic-formula-with-old] simply also allows the use of the `Old` operator.

###### `Old` operator
When writing postconditions, one may write (Old (recdef ..vars..)) to refer to the recdef as defined at the beginning of the program.

###### SLFL-Formulas
> [sl-formula] :=                      True | False <br> 
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (= var1 var2) | (not (= var1 var2)) | (= var1 nil) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (not (= var1 nil)) | (= var1 (func1 var2)) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| [set-formula] | [int-formula] <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (* [sl-formula] [sl-formula]) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; | (and [sl-formula] [sl-formula]) <br> 
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;|  (nonsepand [sl-formula] [sl-formula]) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (or [sl-formula] [sl-formula]) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (ite [sl-formula] [sl-formula] [sl-formula]) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (Exists (= var1 (func1 var2)) [sl-formula]) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (boolean-recfunc ..vars..)   

> [set-formula] := [locset-formula] | [boolset-formula] | [intset-formula]

> [locset-formula] := (= [locset-term] [locset-term]) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (IsMember var1 [locset-term]) <br> 
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (IsSubset [locset-term] [locset-term]) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (Not [locset-formula])
> <br><br>
> [locset-term] := EmptySetLoc | (locset-recfunc ..vars..) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; |(SetAdd [locset-term] var1) | (SetDel [locset-term] var1) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; | (SetIntersect [locset-term] [locset-term]) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; | (SetUnion [locset-term] [locset-term]) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp; | (ite [sl-formula] [locset-term] [locset-term])
> <br><br>
> \> [set-formula] and [set-term] above are defined for sets of `Loc`s. They can also be defined for `Bool`, `Int` with variables, recursive-functions of the appropriate sorts, and whose corresponding empty sets are `EmptySetBool` and `EmptySetInt`.


> [int-formula] := (< [int-term] [int-term]) | (> [int-term] [int-term]) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (<= [int-term] [int-term]) | (>= [int-term] [int-term]) <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (= [int-term] [int-term]) | (not [int-formula])
> <br><br>
> [int-term] := (IntConst [int]) | (intfunc locvar)| intvar <br>
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;| (+ [int-term] [int-term]) | (- [int-term] [int-term])


A singly linked list can be defined as follows: 
> (RecDef (List x) (ite (= x nil) True (Exists (= y (next x)) (* (= (next x) (next x)) (List y)))))

The lists List(x) and List(y) are disjoint: 
> (* (List x) (List y))

###### FL-formulas
FL formulas are written similarly. In FL, heap heap properties are denoted using

- (Sp ...) - the `support` operator. The support of ab FL term/formula is the portion of the heap upon which the formula depends.
- (antiSp ...) - the `cloud` operator. A clouded FL term/formula acts as if it is supportless, i.e (Sp (antSp ...)) is empty.

See [cite paper] for the syntax of FL.

A singly linked list can be defined as follows: 
> (RecDef (List x) (ite (= x nil) True (and (List (next x)) (not (IsMember x (Sp (List (antiSp (next x)))))))))

The lists List(x) and List(y) are disjoint: 
> (and (List x) (List y) (= EmptySetLoc (SetIntersect (Sp (List x)) (Sp (List y)))) )