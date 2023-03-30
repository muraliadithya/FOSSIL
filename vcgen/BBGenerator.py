"""
Grammar for programming front-end

Thing := printable
Expr := Thing | ( Expr^+ )
SubstitutableExpr := Expr

Decls := Expr^+
Lemmas := Expr^*

Params := (Thing^+)
ProgName := Thing
ProgDecl := (Program ProgName Params)

PreCondition := (Pre SubstitutableExpr)
PostCcondition := (Post SubstitutableExpr)

SkipStmt := (skip)
AssignStmt := (assign Expr Expr)
AssumeStmt := (assume Expr)
AllocStmt := (alloc Expr)
FreeStmt := (free Expr)
CallStmt := (call ProgName Params)
ReturnStmt := (return)
Statement := SkipStmt | AssignStmt | AssumeStmt | AllocStmt |
             FreeStmt | CallStmt | Return Stmt | (If Expr Then Program Else Program)
Program := Statement^+

FrontEnd := Decls Lemmas [ProgDecl PreCondition PostCondition Program]^+
"""


import pyparsing as pp


"""
The parsing happens in two phases. The first phase collects the programs appearing in the input and collects their
signature (name and input parameters) as well as their contracts. There is no type checking, checking if variables 
have been declared, or anything fancy because this is meant to be a bare-minimum parser to simply generate 
basic blocks. The basic block to VC generation pipeline must handle these checks.
"""


LParen = pp.Literal('(').suppress()
RParen = pp.Literal(')').suppress()


class _ProgDeclParser:
    """
    Phase 1 parser for reading program declarations to record signatures and contracts
    """
    def __init__(self):
        # Attribute used to store the parser element
        self.ProgDeclParser = None
        # Global state for bookkeeping while parsing
        self.contracts = dict()

    def _make_parser(self):
        Keywords = pp.one_of("Program Pre Post")
        Thing = ~Keywords + pp.Word(pp.alphanums + '=+-*_<>')

        TextExpr = pp.Forward()
        TextExpr <<= pp.original_text_for(Thing ^ (LParen + TextExpr[1, ...] + RParen))

        SubstitutableExpr = pp.Forward()
        SubstitutableExpr <<= Thing ^ (LParen + SubstitutableExpr[1, ...] + RParen)

        @SubstitutableExpr.set_parse_action
        def parse_substitutable_expr(string, loc, tokens):
            if len(tokens) == 1:
                return tokens[0]
            else:
                expr_as_list = [list(tokens)]
                # return expr_to_str(expr_as_list), expr_as_list
                return expr_as_list

        Params = LParen + Thing[1, ...] + RParen

        @Params.set_parse_action
        def parse_params(string, loc, tokens):
            return [tokens]

        ProgName = Thing.copy()
        ProgDecl = LParen + pp.Literal("Program").suppress() + ProgName + Params + RParen
        PreCondition = LParen + pp.Literal("Pre").suppress() + SubstitutableExpr + RParen
        PostCondition = LParen + pp.Literal("Post").suppress() + SubstitutableExpr + RParen
        ProgDeclBlock = ProgDecl + PreCondition + PostCondition

        @ProgDeclBlock.set_parse_action
        def parse_prog_decl_block(string, loc, tokens):
            prog_name, params, precondition, postcondition = tokens
            self.contracts[prog_name] = {'params': params, 'pre': precondition, 'post': postcondition}
            # return prog_name

        ProgDeclFormat = TextExpr[1, ...] + (ProgDeclBlock + TextExpr[1, ...])[1, ...]
        self.ProgDeclParser = ProgDeclFormat

    def get_declarations(self, input_string):
        self._make_parser()
        decl_parser = self.ProgDeclParser
        decl_parser.parse_string(input_string)
        contracts = self.contracts
        # Wipe self.contracts so it can be used again
        self.contracts = dict()
        return contracts


class _BBWrapper:
    """
    Auxiliary class for wrapping parsed results of programs
    """
    def __init__(self, bbs):
        self.bbs = bbs

    def __str__(self):
        return str(self.bbs)

    def __repr__(self):
        return self.__str__()

    def to_bbs(self):
        return self.bbs


class BBGenerator:
    """
    Primary class for generating basic blocks from programs. Uses the results of the Phase 1 parser and does
    Phase 2 parsing of the input into basic blocks. The primary function is parse_input which takes a string and
    returns a list of basic blocks.
    """

    def __init__(self):
        # Attribute used to store the parser element
        self.FrontEnd = None
        # Global state for bookkeeping while parsing
        self.basic_blocks = []
        self.contracts = dict()
        self.decls_and_lemmas = None

    def _make_parser(self):
        Keywords = pp.one_of("Program Pre Post skip assign assume alloc free call return If Then Else")
        Thing = ~Keywords + pp.Word(pp.alphanums + '=+-*_<>')

        TextExpr = pp.Forward()
        TextExpr <<= pp.original_text_for(Thing ^ (LParen + TextExpr[1, ...] + RParen))

        SubstitutableExpr = pp.Forward()
        SubstitutableExpr <<= Thing ^ (LParen + SubstitutableExpr[1, ...] + RParen)

        # Commented out functionality is handled in ProgDeclParser
        # @SubstitutableExpr.set_parse_action
        # def parse_substitutable_expr(string, loc, tokens):
        #     if len(tokens) == 1:
        #         return tokens[0]
        #     else:
        #         expr_as_list = [list(tokens)]
        #         # return expr_to_str(expr_as_list), expr_as_list
        #         return expr_as_list

        # performs simultaneous substitution, where the substitution is given as a list of pairs of (pattern, replacement)
        def substitute_expr(expr_as_list, replacement_scheme):
            if type(expr_as_list) != list:
                for pattern, replacement in replacement_scheme:
                    if expr_as_list == pattern:
                        return replacement
                return expr_as_list
            else:
                return [substitute_expr(e, replacement_scheme) for e in expr_as_list]

        def expr_to_str(expr_as_list):
            if type(expr_as_list) != list:
                return expr_as_list
            else:
                return '(' + ' '.join([expr_to_str(e) for e in expr_as_list]) + ')'

        Decls_And_Lemmas = TextExpr[1, ...]

        Params = LParen + Thing[1, ...] + RParen

        @Params.set_parse_action
        def parse_params(string, loc, tokens):
            return [tokens]

        ProgName = Thing.copy()
        ProgDecl = LParen + pp.Literal("Program").suppress() + ProgName + Params + RParen
        PreCondition = LParen + pp.Literal("Pre").suppress() + SubstitutableExpr + RParen
        PostCondition = LParen + pp.Literal("Post").suppress() + SubstitutableExpr + RParen
        ProgDeclBlock = ProgDecl + PreCondition + PostCondition

        Program = pp.Forward()
        Statement = pp.Forward()
        SkipStmt = LParen + pp.Literal("skip") + RParen
        AssignStmt = LParen + pp.Literal("assign") + TextExpr + TextExpr + RParen
        AssumeStmt = LParen + pp.Literal("assume") + TextExpr + RParen
        AllocStmt = LParen + pp.Literal("alloc") + Thing + RParen
        FreeStmt = LParen + pp.Literal("free") + Thing + RParen
        CallStmt = LParen + pp.Literal("call").suppress() + ProgName + Params + RParen
        ReturnStmt = LParen + pp.Literal("return").suppress() + RParen
        ITEStmt = LParen + pp.Literal("If").suppress() + TextExpr + pp.Literal(
            "Then").suppress() + Program + pp.Literal("Else").suppress() + Program + RParen
        BasicStmt = SkipStmt ^ AssignStmt ^ AssumeStmt ^ AllocStmt ^ FreeStmt
        Statement <<= BasicStmt ^ CallStmt ^ ReturnStmt ^ ITEStmt  # Write basic statement last as it should only apply when others do not
        Program <<= Statement[1, ...]

        ProgramBlock = ProgDeclBlock + Program
        FrontEnd = Decls_And_Lemmas + ProgramBlock[1, ...]

        @BasicStmt.set_parse_action
        def parse_basic_stmt(string, loc, tokens):
            return _BBWrapper([[f"({' '.join(tokens)})"]])

        @CallStmt.set_parse_action
        def parse_call_stmt(string, loc, tokens):
            prog_name, actual_params = tokens
            formal_params = self.contracts[prog_name]['params']
            formal_pre = self.contracts[prog_name]['pre']
            formal_post = self.contracts[prog_name]['post']
            assert len(formal_params) == len(actual_params)
            replacement_scheme = [(formal_params[i], actual_params[i]) for i in range(len(formal_params))]
            actual_pre = expr_to_str(substitute_expr(formal_pre, replacement_scheme))
            actual_post = expr_to_str(substitute_expr(formal_post, replacement_scheme))
            return _BBWrapper([[f'(RelaxedPost {actual_pre})', '<!END!>'], [f'(call {actual_pre} {actual_post})']])

        @ReturnStmt.set_parse_action
        def parse_return_stmt(string, loc, tokens):
            return _BBWrapper([['<!RETURN!>', '<!END!>']])

        @ITEStmt.set_parse_action
        def parse_ite_stmt(string, loc, tokens):
            cond_expr, wrapped_then_prog, wrapped_else_prog = tokens
            then_prog = wrapped_then_prog.to_bbs()
            else_prog = wrapped_else_prog.to_bbs()
            assume_stmt = f'(assume {cond_expr})'
            negated_assume_stmt = f'(assume (not {cond_expr}))'
            then_bbs = [[assume_stmt] + bb for bb in then_prog]
            else_bbs = [[negated_assume_stmt] + bb for bb in else_prog]
            return _BBWrapper(then_bbs + else_bbs)

        @Program.set_parse_action
        def parse_program(string, loc, tokens):
            # Disambiguate between one statement and many
            tokens = list(tokens)
            if type(tokens[0]) != _BBWrapper:
                statement_bbs_list = [tokens]
            else:
                statement_bbs_list = [tt.to_bbs() for tt in tokens]
            finished_bbs = []
            current_bbs = [[]]
            for statement_bbs in statement_bbs_list:
                current_bbs = [current_bb + statement_bb for current_bb in current_bbs for statement_bb in
                               statement_bbs]
                new_bbs = [bb for bb in current_bbs if '<!END!>' in bb]
                finished_bbs += new_bbs
                current_bbs = [bb for bb in current_bbs if '<!END!>' not in bb]
            if not finished_bbs:
                return _BBWrapper(current_bbs)
            else:
                return _BBWrapper([bb for bb in finished_bbs] + current_bbs)

        @ProgDeclBlock.set_parse_action
        def parse_prog_decl_block(string, loc, tokens):
            # Commented out functionality is handled in ProgDeclParser
            # prog_name, params, precondition, postcondition = tokens
            # self.contracts[prog_name] = {'params': params, 'pre': precondition, 'post': postcondition}
            prog_name = tokens[0]
            return prog_name

        @ProgramBlock.set_parse_action
        def parse_program_block(string, loc, tokens):
            prog_name, wrapped_bbs = tokens
            bbs = wrapped_bbs.to_bbs()
            # Remove <!END!> tag from the end of bbs
            bbs = [bb[:-1] for bb in bbs]
            precondition = f"(Pre {expr_to_str(self.contracts[prog_name]['pre'])})"
            postcondition = f"(Post {expr_to_str(self.contracts[prog_name]['post'])})"
            bbs = [[precondition] + bb for bb in bbs]
            bbs = [bb[:-1] + [postcondition] if bb[-1] == '<!RETURN!>' else bb for bb in bbs]
            self.basic_blocks += bbs

        @Decls_And_Lemmas.set_parse_action
        def parse_decls_and_lemmas(string, loc, tokens):
            return [list(tokens)]

        @FrontEnd.set_parse_action
        def parse_front_end(string, loc, tokens):
            self.decls_and_lemmas = tokens[0]
            # Add the declarations before the beginning of each basic block
            self.basic_blocks = [self.decls_and_lemmas + bb for bb in self.basic_blocks]

        FrontEnd = FrontEnd.ignore(pp.cpp_style_comment)
        return FrontEnd

    def parse_input(self, input_string):
        self.contracts = _ProgDeclParser().get_declarations(input_string)
        front_end_parser = self._make_parser()
        front_end_parser.parse_string(input_string)
        return self.basic_blocks
