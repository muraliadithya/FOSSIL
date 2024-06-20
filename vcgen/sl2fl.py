import pyparsing as pp



# from BBGenerator import BBGenerator
# from preprocessing import ml_to_sl


LParen = pp.Literal('(').suppress()
RParen = pp.Literal(')').suppress()


Thing = pp.Word(pp.alphanums + '=+-*_<>:')

Expr = pp.Forward()
Expr <<= Thing ^ (LParen + Expr[1, ...] + RParen)


@Expr.set_parse_action
def parse_expr(string, loc, tokens):
    if len(tokens) == 1:
        return tokens[0], tokens[0]
    else:
        expr = list(tokens)
        # if expr[0][0] == 'or':
        #     raise ValueError("or operand not supported in SL")
        # and operator
        if expr[0][0] == 'and':
            # assert len(expr) == 3, "and operator can only have two operands"
            formulas = [subexpr[0] for subexpr in expr[1:]]
            sp_formulas = [subexpr[1] for subexpr in expr[1:]]
            return_expr = ['and'] + formulas + [['='] + list(['Sp', subexpr] for subexpr in sp_formulas)]
            sp_expr = formulas[0]
        # separating conjunction operator
        elif expr[0][0] == '*':
            assert len(expr) == 3, "separating conjunction operator can only have two operands"
            formulas = [subexpr[0] for subexpr in expr[1:]]
            sp_formulas = [subexpr[1] for subexpr in expr[1:]]
            return_expr = ['and'] + formulas + [['=', 'EmptySetLoc', ['SetIntersect', ['Sp', sp_formulas[0]], ['Sp', sp_formulas[1]]]]]
            sp_expr = ['and'] + formulas
        # existential quantifier
        elif expr[0][0] == 'Exists':
            # assert len(expr) == 3, "Existential quantifier handles only one variable, has a guard ((= exists_var expr)), and a body"
            guard_exprs = [subexpr[0] for subexpr in expr[1:-1]]
            assert all(subexpr[0] == '=' and type(subexpr[1]) == str for subexpr in guard_exprs)
            guard_var_term_pairs = [(subexpr[1], subexpr[2]) for subexpr in guard_exprs]
            existential_matrix = expr[-1][0]
            for guard_var, guard_term in guard_var_term_pairs:
                existential_matrix = substitute(existential_matrix, guard_var, ['antiSp', guard_term])
            return_expr = ['and'] \
                          + [['=', guard_term, guard_term] for _, guard_term in guard_var_term_pairs] \
                          + [existential_matrix]
            sp_expr = return_expr
        else:
            return_expr = [subexpr[0] for subexpr in expr]
            sp_expr = return_expr
        return return_expr, sp_expr



def substitute(expr_as_list, old, new):
    if type(expr_as_list) == str:
        if expr_as_list == old:
            return new
        else:
            return expr_as_list
    else:
        return [substitute(subexpr, old, new) for subexpr in expr_as_list] 


def expr_to_str(expr_as_list):
    if type(expr_as_list) == str:
        return expr_as_list
    else:
        return '(' + ' '.join([expr_to_str(e) for e in expr_as_list]) + ')'



def sl_to_fl(slexpr_str):
    flexpr = Expr.parse_string(slexpr_str)
    #assert len(flexpr) == 1
    #print(flexpr)
    flexpr_str = expr_to_str(flexpr[0][0])
    return flexpr_str

# This is how you test one string at a time
sltest = """(ite (= x nil) True
                       (Exists (= y (next x))  (* (= (next x) (next x)) (List y)))
                   )"""

sltest = """
(Post (and (BST ret)
  (= (Keys ret) (SetAdd (Old (Keys x)) k))
  (ite (< k (Old (Min x))) (= (Min ret) k) (= (Min ret) (Old (Min x))))
  (ite (> k (Old (Max x))) (= (Max ret) k) (= (Max ret) (Old (Max x))))
  (= (BH ret) (Old (BH x)))
    (Exists (= lft (left ret)) (= rht (right ret)) (= cl (color lft)) (= cr (color rht))
      (* (ite (Black ret) True (ite (Old (Black x))
                        (and (ite (= lft nil) True (= cl (IntConst 1))) (ite (= rht nil) True (= cr (IntConst 1))) )
                        (or (ite (= lft nil) True (= cl (IntConst 1))) (ite (= rht nil) True (= cr (IntConst 1))) )
                        ))
          (and (= (BH lft) (BH rht)) (* (RBT lft) (RBT rht)))
      )
    )
))
"""

print("Original:\n", sltest, "\n", "Translated:\n", sl_to_fl(sltest), "\n\n")

exit(0)

# This is how you test several strings
sltests = [
# Should print out the same expr as there are no sl-specific operators
"""(ite (= x nil) EmptySetInt
                      (SetAdd (Keys (next x)) (key x)))""",
"""(ite (= x nil) True
                        (Exists (= y (next x))  (* (= (next x) (next x)) (List y)))
                    )""",
"""(* (List x) (List y))""",
"""(and (List ret) (= (Keys ret) (SetUnion (Old (Keys x)) (Old (Keys y)))) )"""
]



# Test:
# This is a test program as a string.

test_prog = """
(Function key   Loc Int)
(Function left  Loc Loc)
(Function right Loc Loc)

(RecFunction Min  Loc Int)
(RecFunction Max  Loc Int)
(Var plus_infty Int)
(Var minus_infty Int)

(RecFunction BST  Loc Bool)
(RecFunction Keys Loc SetInt)

(Var x Loc)

(RecDef (Min x) (ite (= x nil) plus_infty
                (ite (<= (key x) (Min (left x)))
                  (ite (<= (key x) (Min (right x)))
                    (key x)
                    (Min (right x))
                  )
                  (ite (<= (Min (left x)) (Min (right x)))
                    (Min (left x))
                    (Min (right x))
                  )
                )))
(RecDef (Max x) (ite (= x nil) minus_infty
                (ite (>= (key x) (Max (left x)))
                  (ite (>= (key x) (Max (right x)))
                    (key x)
                    (Max (right x))
                  )
                  (ite (>= (Max (left x)) (Max (right x)))
                    (Max (left x))
                    (Max (right x))
                  )
                )))

(RecDef (BST x) (ite (= x nil) True (Exists (= y (left x)) (Exists (= z (right x)) (Exists (= k (key x))
                                (* (* (= k (key x)) (and (BST y) (< (Max y) k))) (and (BST z) (< k (Min z))))
                          )
                        )
                      )
                ))

(RecDef (Keys x) (ite (= x nil) EmptySetInt
                      (SetAdd (SetUnion (Keys (left x)) (Keys (right x)))
                              (key x))))

(lemma (x) (=> (BST x) (= (Sp (Min x)) (Sp (BST x)))))
(lemma (x) (=> (BST x) (= (Sp (Max x)) (Sp (BST x)))))
(lemma (x) (=> (BST x) (= (Sp (Keys x)) (Sp (BST x)))))

(Var k Int)
(lemma (x) (=> (BST x) (=> (> (Min x) k) (not (IsMember k (Keys x))))))
(lemma (x) (=> (BST x) (=> (< (Max x) k) (not (IsMember k (Keys x))))))

(Var lft Loc)
(Var rht Loc)
(Var right_left Loc)
(Var tmp Loc)
(Var ret Loc)

(Var xl Loc)
(Var xr Loc)

(Program bst_remove_root (x k) (ret))
(Pre (* (not (= x nil)) (and (BST x) (Exists (= lft (left x)) (Exists (= rht (right x)) 
                            (* (* (= k (key x)) (and (BST lft) (< (Max lft) k))) (and (BST rht) (< k (Min rht))))
                          ))
                        )
      )
)
(Post (BST ret))

(If (and (= (left x) nil) (= (right x) nil))
 Then
  (free x)
  (assign ret nil)
  (return)
 Else (If (= (left x) nil)
 Then
  (assign ret (right x))
  (free x)
  (return)
 Else (If (= (right x) nil)
 Then
  (assign ret (left x))
  (free x)
  (return)
 Else
  (assign rht (right x))
  (assign right_left (left rht))

  (assign (right x) right_left)
  (call bst_remove_root (x k) (tmp))
  (assume (< (Max tmp) (key rht)))
  (assign (left rht) tmp)
  (assign ret rht)
  (return)
)))
"""

# # This splits the program into basic blocks.

# bbgen_object = BBGenerator()
# parsed_bbs = bbgen_object.parse_input(test_prog)
# i = 3   # Use the 0th basic block for now

# # This takes a BB (with no comments) and converts it into a list of strings, one for each 'command' of the BB (in this case, annotated in SL).
# sltests2 = ml_to_sl(parsed_bbs[i])

# # The vcgen tool takes such a list of strings (in FL) and generates VCs. 
# # tool_input = [sl_to_fl(x) for x in sltest2]

# for sltest_str in sltests2:
#     if sltest_str.startswith('(RecDef') or sltest_str.startswith('(Pre') or sltest_str.startswith('(Post'):
#         print("Original:\n", sltest_str)
#         print("Translated:\n",sl_to_fl(sltest_str), "\n\n")


# print(sl_to_fl('(True)'))




# print('This:')
# print(sl_to_fl( '(* (List x) (List y)) (and (List ret) (= (Keys ret) (SetUnion (Old (Keys x)) (Old (Keys y)))))' ))
