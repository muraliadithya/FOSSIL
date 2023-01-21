from BBGenerator import BBGenerator


# Programs below are nonsense and only intended to be used for testing purposes
# as they mimic the 'form' of real inputs

one_prog = """
(Const nil Loc)
(Var var1 Loc)
(Function next1 Loc Loc)
(Function next2 Loc Loc)
(Lemma (var1 Loc) (= var1 var1))

(Program my_func (x y))
(Pre (= x (next1 y)))
(Post (= y nil))
(If (= x nil)
Then
    (If (= x y)
    Then
    (assign x (f y))
    (return)
    Else
    (alloc z)
    (call my_func (y z))
    (assume (not (= z nil)))
    )
Else
(free z)
)
(return)
"""

two_prog = """
(Const nil Loc)
(Var var1 Loc)
(Function next1 Loc Loc)
(Function next2 Loc Loc)
(Lemma (var1 Loc) (= var1 var1))

(Program my_func1 (x y))
(Pre (= x (next1 y)))
(Post (= y nil))
(If (= x nil)
Then
    (If (= x y)
    Then
    (assign x (f y))
    (return)
    Else
    (alloc z)
    (call my_func2 (y z))
    (assume (not (= z nil)))
    )
Else
(free z)
)
(return)

(Program my_func2 (x y))
(Pre (= x (next2 y)))
(Post (= y nil))
(If (= x nil)
Then
(assign x x)
(call my_func2 (y z))
(assume (not (= z nil)))
Else
(skip)
)
(return)
"""

test_prog = """
(Const nil Loc)
(Function next Loc Loc)
(Var var1 Loc)
(RecFunction List Loc Bool)
(RecDef (List var1) (ite (= var1 nil) True (and (not (IsMember (var1)  (SPList (next var1)))) (List (next var1)))) )

(Program this1 (x y z))
(Pre (List x))
(Post (List y))
(assume (not (= x nil)))
(assign y (next x))
(assume (not (= y nil)))
(assign z (next y))
(assign (next x) z)

(return)
"""

real_prog = """
(Var var1 Loc)
(Const nil Loc)
(Const plus_infty Int)
(Function left Loc Loc)
(Function right Loc Loc)
(Function key Loc Int)
(RecFunction Mintree Loc Int)
(RecDef (Mintree var1) (ite (= var1 nil) plus_infty
                            (ite (< (key var1) (Mintree (left var1)) )
                                 (ite (< (key var1) (Mintree (right var1)) ) (key var1) (Mintree (right var1))  )
                                 (ite (< (Mintree (left var1)) (Mintree (right var1))) (Mintree (left var1)) (Mintree (right var1)) )  
                              )
                         )
)





(Program bst_delete_rec (x))
(Pre True)
(Post True)
(assign x x)
(return)
"""

bbgen_object = BBGenerator()
parsed_bbs = bbgen_object.parse_input(real_prog)
print(f'{str(len(parsed_bbs))} Basic Blocks\n', '\n'.join(parsed_bbs[0]))
