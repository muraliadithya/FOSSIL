**Notes on writing VCs for the Frame Logic tool**

								
->(Var x type)							Variable declaration where 'x' is the name and 'type' is the type
									'nil' is instantiated automaticallly.
->(Const x type)
-> Types: Loc Int SetLoc SetInt (Loc is the forground sort)

->(Function f type1 type2... typen	rtype)		Creates uninterpreted function 'f'. Inputs of type1 typ2... and returns rtype

->(RecFunction f t1 t2...tn	rt)					
  (RecDef (f x1 x2 ... xn)	X )				Creates a recursive function followed by its definition, written over the free
									variables x1,x2,...xn. The two do not have to be written back to back. The name
									'f' should not start with 'SP'.

->(lemma (x1 x2 .. xn) X)					Lemmas are instantiated over the same 'versions' of functions. 

->(Pre X)								Precondition
->(Post X)								Postcondition. This not only checks that X is true, but also that the support of X is 
									exactly the locations being kept track of. There are two variants to this that the tool allows.
->(RelaxedPost X)							Check if X is true and if the support of X is containted in the locations being kept track of
->(SupportlessPost X)						Check if X is true.
->(assume X)							Assume
->(assign x y)							Assign y to location x. x := y
->(assign (f x1 .. xn) y)					Mutation. f'(x) := if (x == x1 .. xn) then y else f
->(alloc x)								Adds a new location x into the heap. (Feature not complete yet)
->(free x)								Frees x from the part of the heap being kept track of.

->(call P (x1 x2 .. xn) (y1 y2 ... yk))   Function call. P, along with its Precondition, Postcondition and some program associated with it
									      has to be defined. If P's precondition is satisfied before the call (and the locations associated
									      are in the current heap), the function is called (for the vc this means just assuming the 											postcondition to P is now satisfied). In terms of heaps, the locations mentioned earlier are
									      discarded and the locations after the function is called are added (Support of the postcondition of 										P(x1 x2.. xn).
									      x1,x2...xn, y1, y2 ... yk must be defined variables.
									      (call P ((f x) x2 ... x) (...)) will give an error. For this, just assign (f x) to a variable beforehand.

Here, 
X := x | (not X) | (= X X)| (or X ..  X)|(and X .. X) | (=> X X)| |(IsMember x Y)| (IsSubSet Y Y) | (< A A) | (<= A A) | (> A A) | (>= A A) | (= A A)
		| (Sp X) | (antiSp X)
Y : = EmptySetInt| EmptySetLoc|(SetAdd Y x)| (SetDel Y x)| (SetIntersect Y Y)| (SetUnion Y Y)
A := a | (IntCont n)| (+ A A)| (- A A)

(Sp X) finds the support of4:30pm X. (antiSp X) acts as a tag that says to not check the support of X, i.e (Sp (antiSp X)) = EmptySetLoc. Otherwise, (antiSp X) does nothing ((antiSp X) = X). Note this only applies one way (antiSp (Sp X)) =/= EmptySetLoc.


A file should start with variable, constant and function declarations, definitions for Recursive funtions, and lemmas. Programs are writte as:
(Program P (in1 in2 ... ink) (out1 out2 ... outm))
(Pre precondtion of P)
(Post postconditon of P)
	|
 body of the program
	|
(return)


Sample program that checks if swapping the first two elements of a list is still a list:

(Var var1 Loc)

(Function next Loc Loc)
(Function key Loc Int)

(RecFunction List Loc Bool)
(RecDef (List var1) (ite (= var1 nil) True (and (not (IsMember (var1)  (Sp (List (antiSp (next var1)))))) (List (next var1)))) )
(Var x Loc)
(Var y Loc)
(Var z Loc)

(Program swaptwo (x))
(Pre (List x))
(Post
 (List x)
)
(assume (not (= x nil)))
(assign y (next x))
(assume (not (= y nil)))
(assign z (next y))
(assign (next x) z)
(assign (next y) x)
(assign x y)
(return)








 
   

























