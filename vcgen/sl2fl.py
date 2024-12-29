import pyparsing as pp
pp.ParserElement.enablePackrat()

LParen = pp.Literal('(').suppress()
RParen = pp.Literal(')').suppress()


Thing = pp.Word(pp.alphanums + '=+-*_<>:')

Expr = pp.Forward()
Expr <<= Thing ^ (LParen + Expr[1, ...] + RParen)


### Attribute to denote propagation of emptyset ###
emptysetprop = True
supportless_operators = ['IntConst','True','False','Old','EmptySetLoc', 'antiSp']
union_operators = ['=', 'not', 'or', 'and', 'nonsepand', '*', '=>', 'IsMember', 'IsSubset', 'SetAdd', 'SetDel','SetIntersect', 'SetUnion', '<', '>', '>=', '<=', '+', '-']


@Expr.set_parse_action
def parse_expr(string, loc, tokens):
    if len(tokens) == 1:
        return tokens[0], tokens[0], True
    else:
        expr = list(tokens)
        # Handle the empty set propagation bit separately
        if expr[0][0] in supportless_operators:
            emp_prop = True
        elif expr[0][0] in union_operators:
            subexpr_props = [subexpr[2] for subexpr in expr[1:]]
            emp_prop = all(subexpr_props)
        else:
            emp_prop = False

        if expr[0][0] == 'and':
            # assert len(expr) == 3, "and operator can only have two operands"
            formulas = [subexpr[0] for subexpr in expr[1:]]
            sp_formulas = [subexpr[1] for subexpr in expr[1:]]
            return_expr = ['and'] + formulas + [['='] + list(['Sp', subexpr] for subexpr in sp_formulas)]
            sp_expr = formulas[0]
        elif expr[0][0] == 'nonsepand':
            assert len(expr) == 3, "nonsepand operator can only have two operands"
            formulas = [subexpr[0] for subexpr in expr[1:]]
            sp_formulas = [subexpr[1] for subexpr in expr[1:]]
            return_expr = ['and'] + formulas
            sp_expr = ['and'] + sp_formulas
        # separating conjunction operator
        elif expr[0][0] == '*':
            assert len(expr) == 3, "separating conjunction operator can only have two operands"
            formulas = [subexpr[0] for subexpr in expr[1:]]
            sp_formulas = [subexpr[1] for subexpr in expr[1:]]
            subexpr_props = [subexpr[2] for subexpr in expr[1:]]
            if any(subexpr_props) and emptysetprop:
                return_expr = ['and'] + formulas
            else:
                return_expr = ['and'] + formulas + [['=', 'EmptySetLoc', ['SetIntersect', ['Sp', sp_formulas[0]], ['Sp', sp_formulas[1]]]]]
            sp_expr = ['and'] + sp_formulas
        # existential quantifier
        elif expr[0][0] == 'Exists':
            # assert len(expr) == 3, "Existential quantifier handles only one variable, has a guard ((= exists_var expr)), and a body"
            guard_exprs = [subexpr[0] for subexpr in expr[1:-1]]
            assert all(subexpr[0] == '=' and type(subexpr[1]) == str for subexpr in guard_exprs)
            guard_var_term_pairs = [(subexpr[1], subexpr[2]) for subexpr in guard_exprs]
            existential_matrix = expr[-1][0]
            sp_existential_matrix = expr[-1][1]
            for guard_var, guard_term in guard_var_term_pairs:
                existential_matrix = substitute(existential_matrix, guard_var, ['antiSp', guard_term])
                sp_existential_matrix = substitute(sp_existential_matrix, guard_var, ['antiSp', guard_term])
            return_expr = ['and'] \
                          + [['=', guard_term, guard_term] for _, guard_term in guard_var_term_pairs] \
                          + [existential_matrix]
            sp_expr = ['and'] \
                          + [['=', guard_term, guard_term] for _, guard_term in guard_var_term_pairs] \
                          + [sp_existential_matrix]
        else:
            return_expr = [subexpr[0] for subexpr in expr]
            sp_expr = return_expr
        return return_expr, sp_expr, emp_prop


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
    flexpr_str = expr_to_str(flexpr[0][0])
    return flexpr_str