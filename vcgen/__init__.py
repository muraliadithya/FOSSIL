"""
% MAIN
% Grammar for programs with annotations:

% Declarations
VarName -> alphanumeric
FuncName -> alphanumeric
Type -> Loc | Int | SetLoc | SetInt | Bool

VarDecl -> Var VarName Type
FuncDecl -> Function FuncName Type Type ...
RecFuncDecl -> RecFunction FuncName Type Type ...
FODecl -> VarDecl | FuncDecl | RecFuncDecl
FODecls -> FODecl FODecl ...     % empty set of fields not allowed
Application -> VarName                               |
               Function(Application, Application ...)  % empty set of arguments not allowed

RecFun -> Def FuncName(VarName, VarName, ... VarName) := Term(Application) % see grammar 'COMBINATOR' below
RecPred -> Def FuncName(VarName, VarName, ... VarName) := Formula(Application) % see grammar 'COMBINATOR' below
RecDef -> RecFun | RecPred
RecDefs -> RecDef RecDef ...     % empty set of recdefs allowed if there are no RecFuncDecl statements
Decls -> FODecls RecDecls

% Annotations
PreFormula -> @pre: Formula(Application) % see grammar 'COMBINATOR' below
PostFormula -> @post: Formula(Application) % see grammar 'COMBINATOR' below

% Program statements
ProgTerm -> VarName | ProgTerm.FuncName % only arity 1 functions can be mutable fields and usable in program terms (no arbitrary uninterpreted functions)
ProgCond -> Formula(ProgTerm) % see grammar 'COMBINATOR' below
AssumeStatement -> assume ProgCond
AssignOrMutateStatement -> ProgTerm := ProgTerm
Statement -> AssumeStatement | AssignOrMutateStatement
Program -> Statement Statement ...

Input -> Decls PreFormula Program PostFormula
"""


"""
% COMBINATOR
% Parametric grammar for building terms and formulae from application expressions:
% 'Application' is a nonterminal that is a parameter in this grammar

IntConst -> signed_integers
SetConst -> empSetLoc | empSetInt
BoolConst -> True | False
TermAtom -> IntConst | SetConst | BoolConst | Application
BinTermOp -> + | - | * |     % integer operations
             &         |     % set intersection
             |               % set union/ set addition
Term -> TermAtom             |
        (Term BinTermOp Term)
        (If Formula Then Term Else Term)

% comparison operators are polymorphic
% 'in' denotes set membership
CompOp -> == | != | < | <= | > | >= | in
Atom -> Application       |
        (Term CompOp Term)
Formula -> Atom
           (Formula & Formula)                    |
           (Formula | Formula)                    |
           (Formula => Formula)                   |
           (If Formula Then Formula Else Formula) |
           (! Formula)
"""
