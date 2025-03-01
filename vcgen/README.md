# FL/SLFL Verification Condition Generator Overview

## Table of Contents

1. [Introduction](#introduction)
2. [Hardware Dependencies](#hardware-dependencies)
3. [Getting Started](#getting-started)
4. [Step-by-Step Instructions](#step-by-step-instructions)
5. [Reusability Guide](#reusability-guide)
6. [Attribution](#attribution)


## Introduction

- The artifact contains the Frame Logic Verification tool which generates and proves verification conditions for heap manipulating programs annotated
with Frame Logic (FL) or FL inspired Separation Logic (SLFL) specifications. 

- We provide a suite of benchmarks (annotated in both FL and SLFL) containing programs manipulating various common data structures such as singly-linked lists, doubly-linked lists, binary search trees etc, showcasing that many functional specifications can be expressed in the logics presented in the paper. 

- The tool implements the verification pipline described in section 5 of the paper, facilitating efficient verification of the programs.

## Hardware Dependencies

There are `no` hardware dependencies. The tool was tested on windows, mac, and ubuntu machines.

## Getting Started

### Requirements
- [Python 3.5 or above](https://www.python.org/downloads/)
- [Z3Py](https://pypi.org/project/z3-solver/)
- [Pyparsing 3.2.0 or above](https://pypi.org/project/pyparsing/)


### Installation Guide

1. Install Z3Py and pyparsing.
3. Add the path to the naturalproofs subdirectory to PYTHONPATH - execute `export PYTHONPATH="/path/to/naturalproofs":$PYTHONPATH`.
4. Change directory to `vcgen`.


## Step-by-Step Instructions

- Benchmarks written with SLFL (resp. FL) are in the directory `benchmarksSL` (resp. `verifiedEqSP`). This contains subdirectories categorized by the primary data structure being manipulated, as well an `all` directory containing all the benchmarks.

- To run all the SLFL benchmarks, run `python runbench.py ./benchmarksSL/all/`
    - NOTE: `runbench.py` runs a python script of the form `python ...`. You may need add a symbolic link `python` if your system does not recognize the `python` command:
      You may also replace the command in `runbench.py` (line 61) with the appropriate one (eg: `python3`). 
- To run all the FL benchmarks, run `python runbench.py ./benchmarksFL/all/ --lang fl`.
    - NOTE: The tool assumes specifications are in SLFL by default. Use `--lang fl` when running FL annotated files.
- To run individual files, simply run `python runbench.py ./path-to-file/filename.fsl`
- Additionally, you may log the entire output of the tool by adding `&> name-of-log-file.txt`.  
#### Expected Output and Reproducing the Results in the Paper

The tool converts a `.fsl` file into multiple basic blocks (BBs) by splitting programs into cases based on If-Then-Else staements (see Sec 5.2, second bullet point of the paper). Let us call these 'Main-BB's. For each Main BB, it generates multiple VCs - one corresponding to each sub-BB, and one VC for proving the postconditon valid.

For each Main BB...
1. The tool prints `goal is valid` if it is able to prove the postcondition, and `goal not proven` otherwise.
    - If it is not able to prove a sub-BB, it prints `Obligation not proven. Assuming obligations {the_obligation}`. If the sub-BB involves a function call, it prints `Could not prove the preconditions for the function call {the_function_call_specs}`. The tool assumes these sub-BBs hold and tries to prove the postcondition.
2. The tool prints the number of VCs generated as `Number of VCs generated for BB: {number}`
3. The total execution time for proving the BB as `Time elapsed: {time}`.

For each `.fsl` file, the tool prints the total execution time along with the number of Main BBs as `('{name_of_file)', {time}, {no_of_main_BBs})`.

- The expected output for running all the SLFL (resp. FL) benchmarks can be seen in `logger_sl_all.txt` (resp. `logger_fl_all.txt`). These contain the following information from Table 1 of the paper:
    - The SLFL times correspond to the `SLFL Verif Time (optimized)` column.
    - The FL times correspond to the `FL Verif Time` column.
    - The number of Main BBs correspond to `Number of Basic Blocks`. Note that these are the same in both SLFL and FL.
- The sum of `Number of VCs generated for BB` per file corresponds to the `Number of Permission Checks` column.

- See `example.fsl` for a sample program. The file `logger_example.txt` shows the expected output.

- To turn off SLFL optimization: In line 15 of `sl2fl.py` in the vcgen folder, set `emptysetprop` to `False`. Run the SLFL benchmarks.

## Reusability Guide

To evaluate reusability, simply write programs in a `.fsl` file annotated with SLFL or FL specifications, and call the tool. An overview of writting benchmarks is given below. 


### Structure of a file

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

### Using Lemmas to bridge the gap between FO and FO+lfp

FO+lfp is strictly more expressive than FO. As such, some programs may require lemmas that bridge this gap (see Sec. 6.2.2 of the paper). To see this in action, see `sorted_find_no_lemma.fsl` in the vcgen directory. This file contains a program which checks if a Sorted list contains an element with a particular key. The expected output for this file can be found in `logger_sorted_find_no_lemma.txt`. Observe that the goal for the third Main BB was `not proven`.

We now add the following lemma to the file (see `sorted_find.fsl`):
- (lemma (x) (=> (Sorted x) (=> (< k (Min x)) (not (IsMember k (Keys x))))))
This says if x is a sorted list and k is less than its minimum element, then k is not in the set of keys of the list. The expected output for this file can be found in `logger_sorted_find.txt`. Observe that all VCs are proven `valid` now.

### Declaring the Heaplet of two Recursive definitions as Equal

The user may declare the heaplet of two recursive functions to be the same (see Sec. 6.2.3 of the paper). For instance, the set of locations upon which computing Keys(x) and List(x) depends on are the same.

This declaration is made using the `EqSp` command. For example, (EqSp (List (Keys))) declares that the support of Keys is the same as that of List, and only generates one (common) support defintion.

The tool does not automatically verify this, and it is up to the user to ensure only the correct recursive functions are equated. Such statements can be proven seperately using the tool by writing them as inductive lemmas. For example, we may prove the support of List(x) and Key(x) by writing the program:

(Program temp (x) (ret)) <br>
(Pre (ite (= x nil) True (= (Sp (List (antiSp (next x)))) (Sp (Keys (antiSp (next x))))))) <br>
(Post (= (Sp (List x)) (Sp (Keys x)))) <br>
(return)

Note that the above is *not* a heap program, but simply a programmatic way of writing a lemma, and does not require the heap tightness condition. We may tell the tool to elide the heap condition check with the command `--weaken-alloc 2`. See `./EqSpProofs/lemmaseqspFL/sl_eqsp.fsl` for the full file.

The proofs for all the EqSps used in the benchmarks are written in `./EqSpProofs/lemmaseqspFL/` and `./EqSpProofs/lemmaseqspSL/`. To run these proofs,
- For SLFL: `python runbench.py ./EqSpProofs/lemmaseqspSL/ --weaken-alloc 2` 
- For FL: `python runbench.py ./EqSpProofs/lemmaseqspFL/ --lang fl --weaken-alloc 2`  

### Writing Benchmarks

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

##### `Old` operator
When writing postconditions, one may write (Old (recdef ..vars..)) to refer to the recdef as defined at the beginning of the program.

#### SLFL-Formulas
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

#### FL-formulas
FL formulas are written similarly. In FL, heap properties are denoted using

- (Sp ...) - the `support` operator. The support of ab FL term/formula is the portion of the heap upon which the formula depends.
- (antiSp ...) - the `cloud` operator. A clouded FL term/formula acts as if it is supportless, i.e (Sp (antSp ...)) is empty.

Please see the paper for the syntax of FL.

A singly linked list can be defined as follows: 
> (RecDef (List x) (ite (= x nil) True (and (List (next x)) (not (IsMember x (Sp (List (antiSp (next x)))))))))

The lists List(x) and List(y) are disjoint: 
> (and (List x) (List y) (= EmptySetLoc (SetIntersect (Sp (List x)) (Sp (List y)))) )


## Attribution 

This artifact extends the `natural proofs` library written for the paper Model-Guided Synthesis of Inductive Lemmas for FOL with Least Fixpoints by 
Murali et al. (OOPSLA 2022). 

Our contribution is the `vcgen` subdirectory, which contains the FL/SLFL VC Generator.