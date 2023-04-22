# Copyright 2019 Ingmar Dasseville, Pierre Carbonnelle
#
# This file is part of Interactive_Consultant.
#
# This program is free software: you can redistribute it and/or modify
# it under the terms of the GNU General Public License as published by
# the Free Software Foundation, either version 3 of the License, or
# (at your option) any later version.
#
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
# GNU General Public License for more details.
#
# You should have received a copy of the GNU General Public License
# along with this program.  If not, see <https://www.gnu.org/licenses/>.

"""


(They are monkey-patched by other modules)

"""
from __future__ import annotations

from copy import copy, deepcopy
from collections import ChainMap
from datetime import date
from dateutil.relativedelta import *
from fractions import Fraction
from re import findall
from sys import intern
from textx import get_location
from typing import Optional, List, Union, Tuple, Dict, Set, Any, Callable, TYPE_CHECKING
if TYPE_CHECKING:
    from .Theory import Theory
    from .Assignments import Assignments, Status
    from .Parse import Declaration, SymbolDeclaration, SymbolInterpretation, Enumeration

from .utils import unquote, OrderedSet, BOOL, INT, REAL, DATE, CONCEPT, RESERVED_SYMBOLS, \
    IDPZ3Error, Semantics


class ASTNode(object):
    """superclass of all AST nodes
    """

    def check(self, condition: bool, msg: str):
        """raises an exception if `condition` is not True

        Args:
            condition (Bool): condition to be satisfied
            msg (str): error message

        Raises:
            IDPZ3Error: when `condition` is not met
        """
        if not condition:
            try:
                location = get_location(self)
            except:
                raise IDPZ3Error(f"{msg}")
            line = location['line']
            col = location['col']
            raise IDPZ3Error(f"Error on line {line}, col {col}: {msg}")

    def dedup_nodes(self,
                    kwargs: Dict[str, ASTNode],
                    arg_name:str
                    ) -> Dict[str, ASTNode]:
        """pops `arg_name` from kwargs as a list of named items
        and returns a mapping from name to items

        Args:
            kwargs (Dict[str, ASTNode])
            arg_name (str): name of the kwargs argument, e.g. "interpretations"

        Returns:
            Dict[str, ASTNode]: mapping from `name` to AST nodes

        Raises:
            AssertionError: in case of duplicate name
        """
        ast_nodes = kwargs.pop(arg_name)
        out = {}
        for i in ast_nodes:
            # can't get location here
            assert i.name not in out, f"Duplicate '{i.name}' in {arg_name}"
            out[i.name] = i
        return out

    def annotate(self, idp):
        return  # monkey-patched

    def annotate1(self, idp):
        return  # monkey-patched

    def interpret(self, problem: Any) -> Expression:
        return self  # monkey-patched

    def EN(self):
        pass  # monkey-patched


class Annotations(ASTNode):
    def __init__(self, parent, annotations: List[str]):

        self.annotations = {}
        for s in annotations:
            p = s.split(':', 1)
            if len(p) == 2:
                if p[0] != 'slider':
                    k, v = (p[0], p[1])
                else:
                    # slider:(lower_sym, upper_sym) in (lower_bound, upper_bound)
                    pat = r"\(((.*?), (.*?))\)"
                    arg = findall(pat, p[1])
                    l_symb = arg[0][1]
                    u_symb = arg[0][2]
                    l_bound = arg[1][1]
                    u_bound = arg[1][2]
                    slider_arg = {'lower_symbol': l_symb,
                                'upper_symbol': u_symb,
                                'lower_bound': l_bound,
                                'upper_bound': u_bound}
                    k, v = ('slider', slider_arg)
            else:
                k, v = ('reading', p[0])
            self.check(k not in self.annotations,
                       f"Duplicate annotation: [{k}: {v}]")
            self.annotations[k] = v


class Constructor(ASTNode):
    """Constructor declaration

    Attributes:
        name (string): name of the constructor

        sorts (List[Symbol]): types of the arguments of the constructor

        type (string): name of the type that contains this constructor

        arity (Int): number of arguments of the constructor

        tester (SymbolDeclaration): function to test if the constructor
        has been applied to some arguments (e.g., is_rgb)

        symbol (Symbol): only for Symbol constructors

        lift (bool): whether it is part of a lift vocabulary
    """

    def __init__(self, parent,
                 name: Union[UnappliedSymbol, str],
                 args: List[Accessor]=None):
        self.name = name
        self.sorts = args if args is not None else []

        self.name = (self.name.s.name if type(self.name) == UnappliedSymbol else
                     self.name)
        self.arity = len(self.sorts)

        self.type = None
        self.symbol = None
        self.tester = None
        self.lift = False

    def __str__(self):
        return (self.name if not self.sorts else
                f"{self.name}({', '.join((str(a) for a in self.sorts))})" )

def CONSTRUCTOR(name: Symbol, args=None) -> Constructor:
    return Constructor(None, name, args)


class Accessor(ASTNode):
    """represents an accessor and a type

    Attributes:
        accessor (UnappliedSymbol, Optional): name of accessor function

        type (string): name of the output type of the accessor

        decl (SymbolDeclaration): declaration of the accessor function
    """
    def __init__(self, parent, type: UnappliedSymbol, accessor: UnappliedSymbol=None):
        self.accessor = accessor
        self.type = type.name
        self.decl = None

    def __str__(self):
        return (self.type if not self.accessor else
                f"{self.accessor}: {self.type}" )


class Expression(ASTNode):
    """The abstract class of AST nodes representing (sub-)expressions.

    Attributes:
        code (string):
            Textual representation of the expression.  Often used as a key.

            It is generated from the sub-tree.
            Some tree transformations change it (e.g., instantiate),
            others don't.

        sub_exprs (List[Expression]):
            The children of the AST node.

            The list may be reduced by simplification.

        type (string):
            The name of the type of the expression, e.g., ``bool``.

        co_constraint (Expression, optional):
            A constraint attached to the node.

            For example, the co_constraint of ``square(length(top()))`` is
            ``square(length(top())) = length(top())*length(top()).``,
            assuming ``square`` is appropriately defined.

            The co_constraint of a defined symbol applied to arguments
            is the instantiation of the definition for those arguments.
            This is useful for definitions over infinite domains,
            as well as to compute relevant questions.

        simpler (Expression, optional):
            A simpler, equivalent expression.

            Equivalence is computed in the context of the theory and structure.
            Simplifying an expression is useful for efficiency
            and to compute relevant questions.

        value (Optional[Expression]):
            A rigid term equivalent to the expression, obtained by
            transformation.

            Equivalence is computed in the context of the theory and structure.

        annotations (Dict[str, str]):
            The set of annotations given by the expert in the IDP-Z3 program.

            ``annotations['reading']`` is the annotation
            giving the intended meaning of the expression (in English).

        original (Expression):
            The original expression, before propagation and simplification.

        variables (Set(string)):
            The set of names of the variables in the expression.

        is_type_constraint_for (string):
            name of the symbol for which the expression is a type constraint

    """
    __slots__ = ('sub_exprs', 'simpler', 'value', 'code',
                 'annotations', 'original', 'str', 'variables', 'type',
                 'is_type_constraint_for', 'co_constraint',
                 'questions', 'relevant')

    def __init__(self):
        self.sub_exprs: List[Expression]
        self.simpler: Optional[Expression] = None
        self.value: Optional[Expression] = None

        self.code: str = intern(str(self))
        if not hasattr(self, 'annotations') or self.annotations == None:
            self.annotations: Dict[str, str] = {'reading': self.code}
        elif type(self.annotations) == Annotations:
            self.annotations = self.annotations.annotations
        self.original: Expression = self

        self.str: str = self.code
        self.variables: Optional[Set[str]] = None
        self.type: Optional[str] = None
        self.is_type_constraint_for: Optional[str] = None
        self.co_constraint: Optional[Expression] = None

        # attributes of the top node of a (co-)constraint
        self.questions: Optional[OrderedSet] = None
        self.relevant: Optional[bool] = None

    def __deepcopy__(self, memo):
        """ copies everyting but .original """
        key = self.__str1__()
        val = memo.get(key, None)
        if val is not None:
            return val
        if self.value == self:
            return self
        out = copy(self)
        out.sub_exprs = [deepcopy(e, memo) for e in out.sub_exprs]
        out.variables = deepcopy(out.variables, memo)
        out.simpler = None if out.simpler is None else deepcopy(out.simpler, memo)
        out.co_constraint = (None if out.co_constraint is None
                             else deepcopy(out.co_constraint, memo))
        if hasattr(self, 'questions'):
            out.questions = deepcopy(self.questions, memo)
        memo[key] = out
        return out

    def same_as(self, other: Expression):
        if self.str == other.str:
            return True
        if self.__class__.__name__ == "Number" and other.__class__.__name__ == "Number":
            return float(self.py_value) == float(other.py_value)
        if self.value is not None and self.value is not self:
            return self.value  .same_as(other)
        if self.simpler is not None:
            return self.simpler.same_as(other)
        if other.value is not None and other.value is not other:
            return self.same_as(other.value)
        if other.simpler is not None:
            return self.same_as(other.simpler)

        if (isinstance(self, Brackets)
           or (isinstance(self, AQuantification) and len(self.quantees) == 0)):
            return self.sub_exprs[0].same_as(other)
        if (isinstance(other, Brackets)
           or (isinstance(other, AQuantification) and len(other.quantees) == 0)):
            return self.same_as(other.sub_exprs[0])

        return self.str == other.str and type(self) == type(other)

    def __repr__(self): return str(self)

    def __str__(self):
        if self.value is not None and self.value is not self:
            return str(self.value)
        if self.simpler is not None:
            return str(self.simpler)
        return self.__str1__()

    def __log__(self):  # for debugWithYamlLog
        return {'class': type(self).__name__,
                'code': self.code,
                'str': self.str,
                'co_constraint': self.co_constraint}

    def collect(self,
                questions: OrderedSet,
                all_: bool=True,
                co_constraints: bool=True
                ) -> OrderedSet:
        """collects the questions in self.

        `questions` is an OrderedSet of Expression
        Questions are the terms and the simplest sub-formula that
        can be evaluated.
        `collect` uses the simplified version of the expression.

        all_=False : ignore expanded formulas
        and AppliedSymbol interpreted in a structure
        co_constraints=False : ignore co_constraints

        default implementation for UnappliedSymbol, AIfExpr, AUnary, Variable,
        Number_constant, Brackets
        """
        for e in self.sub_exprs:
            e.collect(questions, all_, co_constraints)

    def collect_symbols(self,
                        symbols: Dict[str, SymbolDeclaration]=None,
                        co_constraints: bool=True
                        ) -> Dict[str, Declaration]:
        """ returns the list of symbol declarations in self, ignoring type constraints
        """
        symbols = {} if symbols == None else symbols
        if self.is_type_constraint_for is None:  # ignore type constraints
            if (hasattr(self, 'decl') and self.decl
                and self.decl.__class__.__name__ == "SymbolDeclaration"
                and not self.decl.name in RESERVED_SYMBOLS):
                symbols[self.decl.name] = self.decl
            for e in self.sub_exprs:
                e.collect_symbols(symbols, co_constraints)
        return symbols

    def collect_nested_symbols(self,
                               symbols: Set[SymbolDeclaration],
                               is_nested: bool
                               ) -> Set[SymbolDeclaration]:
        """ returns the set of symbol declarations that occur (in)directly
        under an aggregate or some nested term, where is_nested is flipped
        to True the moment we reach such an expression

        returns {SymbolDeclaration}
        """
        for e in self.sub_exprs:
            e.collect_nested_symbols(symbols, is_nested)
        return symbols

    def generate_constructors(self, constructors: Dict[str, List[Constructor]]):
        """ fills the list `constructors` with all constructors belonging to
        open types.
        """
        for e in self.sub_exprs:
            e.generate_constructors(constructors)

    def co_constraints(self, co_constraints: OrderedSet):
        """ collects the constraints attached to AST nodes, e.g. instantiated
        definitions
        """
        if self.co_constraint is not None and self.co_constraint not in co_constraints:
            co_constraints.append(self.co_constraint)
            self.co_constraint.co_constraints(co_constraints)
        for e in self.sub_exprs:
            e.co_constraints(co_constraints)

    def is_reified(self) -> bool: return True

    def is_assignment(self) -> bool:
        """

        Returns:
            bool: True if `self` assigns a rigid term to a rigid function application
        """
        return False

    def has_decision(self) -> bool:
        # returns true if it contains a variable declared in decision
        # vocabulary
        return any(e.has_decision() for e in self.sub_exprs)

    def type_inference(self) -> Dict[Variable, Symbol]:
        # returns a dictionary {Variable : Symbol}
        try:
            return dict(ChainMap(*(e.type_inference() for e in self.sub_exprs)))
        except AttributeError as e:
            if "has no attribute 'sorts'" in str(e):
                msg = f"Incorrect arity for {self}"
            else:
                msg = f"Unknown error for {self}"
            self.check(False, msg)

    def __str1__(self) -> str:
        return ''  # monkey-patched

    def update_exprs(self, new_exprs: List[Expression]) -> Expression:
        return self  # monkey-patched

    def simplify1(self) -> Expression:
        return self  # monkey-patched

    def substitute(self,
                   e0: Expression,
                   e1: Expression,
                   assignments: Assignments,
                   tag=None) -> Expression:
        return self  # monkey-patched

    def instantiate(self,
                    e0: List[Expression],
                    e1: List[Expression],
                    problem: Theory=None
                    ) -> Expression:
        return self  # monkey-patched

    def instantiate1(self,
                    e0: Expression,
                    e1: Expression,
                    problem: Theory=None
                    ) -> Expression:
        return self  # monkey-patched

    def simplify_with(self, assignments: Assignments) -> Expression:
        return self  # monkey-patched

    def symbolic_propagate(self,
                           assignments: Assignments,
                           tag: Status,
                           truth: Optional[Expression] = None
                           ):
        return  # monkey-patched

    def propagate1(self,
                   assignments: Assignments,
                   tag: Status,
                   truth: Optional[Expression] = None
                   ):
        return  # monkey-patched

    def translate(self, problem: Theory, vars={}):
        pass  # monkey-patched

    def reified(self, problem: Theory):
        pass  # monkey-patched

    def translate1(self, problem: Theory, vars={}):
        pass  # monkey-patched

    def as_set_condition(self) -> Tuple[Optional[AppliedSymbol], Optional[bool], Optional[Enumeration]]:
        """Returns an equivalent expression of the type "x in y", or None

        Returns:
            Tuple[Optional[AppliedSymbol], Optional[bool], Optional[Enumeration]]: meaning "expr is (not) in enumeration"
        """
        return (None, None, None)

    def split_equivalences(self) -> Expression:
        """Returns an equivalent expression where equivalences are replaced by
        implications

        Returns:
            Expression
        """
        out = self.update_exprs(e.split_equivalences() for e in self.sub_exprs)
        return out

    def add_level_mapping(self,
                          level_symbols: Dict[SymbolDeclaration, Symbol],
                          head: AppliedSymbol,
                          pos_justification: bool,
                          polarity: bool,
                          mode: Semantics
                          ) -> Expression:
        """Returns an expression where level mapping atoms (e.g., lvl_p > lvl_q)
         are added to atoms containing recursive symbols.

        Arguments:
            - level_symbols (Dict[SymbolDeclaration, Symbol]): the level mapping
              symbols as well as their corresponding recursive symbols
            - head (AppliedSymbol): head of the rule we are adding level mapping
              symbols to.
            - pos_justification (Bool): whether we are adding symbols to the
              direct positive justification (e.g., head => body) or direct
              negative justification (e.g., body => head) part of the rule.
            - polarity (Bool): whether the current expression occurs under
              negation.
        """
        return (self.update_exprs((e.add_level_mapping(level_symbols, head, pos_justification, polarity, mode)
                                   for e in self.sub_exprs))
                    .annotate1())  # update .variables

Extension = Tuple[Optional[List[List[Expression]]],  # None if the extension is infinite (e.g., Int)
                  Optional[Callable]]  # None if filtering is not required

class Symbol(Expression):
    """Represents a Symbol.  Handles synonyms.

    Attributes:
        name (string): name of the symbol
    """
    TO = {'Bool': BOOL, 'Int': INT, 'Real': REAL,
          '`Bool': '`'+BOOL, '`Int': '`'+INT, '`Real': '`'+REAL,}

    def __init__(self, parent, name: str):
        self.name = unquote(name)
        self.name = Symbol.TO.get(self.name, self.name)
        self.sub_exprs = []
        self.decl = None
        super().__init__()
        self.variables = set()
        self.value = self

    def __str__(self):
        return self.name

    def __repr__(self):
        return str(self)

    def has_element(self, term: Expression,
                    interpretations: Dict[str, SymbolInterpretation],
                    extensions: Dict[str, Extension]
                    ) -> Expression:
        """Returns an expression that says whether `term` is in the type/predicate denoted by `self`.

        Args:
            term (Expression): the argument to be checked

        Returns:
            Expression: whether `term` is in the type denoted by `self`.
        """
        self.check(self.decl.out.name == BOOL, "internal error")
        return self.decl.contains_element(term, interpretations, extensions)

def SYMBOL(name: str) -> Symbol:
    return Symbol(None, name)

class Type(Symbol):
    """ASTNode representing `aType` or `Concept[aSignature]`, e.g., `Concept[T*T->Bool]`

    Inherits from Symbol

    Args:
        name (Symbol): name of the concept

        ins (List[Symbol], Optional): domain of the Concept signature, e.g., `[T, T]`

        out (Symbol, Optional): range of the Concept signature, e.g., `Bool`
    """

    def __init__(self, parent,
                 name:str,
                 ins: List[Type]=None,
                 out: Type=None):
        self.ins = ins
        self.out = out
        super().__init__(parent, name)

    def __str__(self):
        return self.name + ("" if not self.out else
                            f"[{'*'.join(str(s) for s in self.ins)}->{self.out}]")

    def __eq__(self, other):
        self.check(self.name != CONCEPT or self.out,
                   f"`Concept` must be qualified with a type signature")
        return (self.name == other.name and
                (not self.out or (
                    self.out == other.out and
                    len(self.ins) == len(other.ins) and
                    all(s==o for s, o in zip(self.ins, other.ins)))))

    def extension(self,
                  interpretations: Dict[str, SymbolInterpretation],
                  extensions: Dict[str, Extension]
                  ) -> Extension:
        pass  # monkey-patched

    def has_element(self,
                    term: Expression,
                    interpretations: Dict[str, SymbolInterpretation],
                    extensions: Dict[str, Extension]
                    ) -> Expression:
        """Returns an Expression that says whether `term` is in the type/predicate denoted by `self`.

        Args:
            term (Expression): the argument to be checked

        Returns:
            Expression: whether `term` `term` is in the type denoted by `self`.
        """
        if self.name == CONCEPT:
            comparisons = [EQUALS([term, c[0]])
                           for c in self.extension(interpretations, extensions)[0]]
            return OR(comparisons)
        else:
            self.check(self.decl.out.name == BOOL, "internal error")
            return self.decl.contains_element(term, interpretations, extensions)

def TYPE(name: str, ins=None, out=None) -> Type:
    return Type(None, name, ins, out)

class AIfExpr(Expression):
    PRECEDENCE = 10
    IF = 0
    THEN = 1
    ELSE = 2

    def __init__(self, parent,
                 if_f: Expression,
                 then_f: Expression,
                 else_f: Expression
                 ) -> AIfExpr:
        self.if_f = if_f
        self.then_f = then_f
        self.else_f = else_f

        self.sub_exprs = [self.if_f, self.then_f, self.else_f]
        super().__init__()

    @classmethod
    def make(cls,
             if_f: Expression,
             then_f: Expression,
             else_f: Expression
             ) -> 'AIfExpr':
        out = (cls)(None, if_f=if_f, then_f=then_f, else_f=else_f)
        return out.annotate1().simplify1()

    def __str1__(self):
        return (f"if {self.sub_exprs[AIfExpr.IF  ].str}"
                f" then {self.sub_exprs[AIfExpr.THEN].str}"
                f" else {self.sub_exprs[AIfExpr.ELSE].str}")

    def collect_nested_symbols(self, symbols, is_nested):
        return Expression.collect_nested_symbols(self, symbols, True)


def IF(IF: Expression,
       THEN: Expression,
       ELSE: Expression,
       annotations=None
       ) -> AIfExpr:
    return AIfExpr.make(IF, THEN, ELSE)


class Quantee(Expression):
    """represents the description of quantification, e.g., `x in T` or `(x,y) in P`
    The `Concept` type may be qualified, e.g. `Concept[Color->Bool]`

    Attributes:
        vars (List[List[Variable]]): the (tuples of) variables being quantified

        subtype (Type, Optional): a literal Type to quantify over, e.g., `Color` or `Concept[Color->Bool]`.

        sort (SymbolExpr, Optional): a dereferencing expression, e.g.,. `$(i)`.

        sub_exprs (List[SymbolExpr], Optional): the (unqualified) type or predicate to quantify over,
        e.g., `[Color], [Concept] or [$(i)]`.

        arity (int): the length of the tuple of variables

        decl (SymbolDeclaration, Optional): the (unqualified) Declaration to quantify over, after resolution of `$(i)`.
        e.g., the declaration of `Color`
    """
    def __init__(self, parent,
                 vars: List[List[Variable]],
                 subtype: Type = None,
                 sort: SymbolExpr = None):
        self.vars = vars
        self.subtype = subtype
        sort = sort
        if self.subtype:
            self.check(self.subtype.name == CONCEPT or self.subtype.out is None,
                   f"Can't use signature after predicate {self.subtype.name}")

        self.sub_exprs = ([sort] if sort else
                          [self.subtype] if self.subtype else
                          [])
        self.arity = None
        for i, v in enumerate(self.vars):
            if hasattr(v, 'vars'):  # varTuple
                self.check(1 < len(v.vars), f"Can't have singleton in binary quantification")
                self.vars[i] = v.vars
                self.arity = len(v.vars) if self.arity == None else self.arity
            else:
                self.vars[i] = [v]
                self.arity = 1 if self.arity == None else self.arity

        super().__init__()
        self.decl = None

        self.check(all(len(v) == self.arity for v in self.vars),
                    f"Inconsistent tuples in {self}")

    @classmethod
    def make(cls,
             var: List[Variable],
             subtype: Type = None,
             sort: SymbolExpr = None
             ) -> 'Quantee':
        out = (cls) (None, [var], subtype=subtype, sort=sort)
        return out.annotate1()

    def __str1__(self):
        signature = ("" if len(self.sub_exprs) <= 1 else
                     f"[{','.join(t.str for t in self.sub_exprs[1:-1])}->{self.sub_exprs[-1]}]"
        )
        return (f"{','.join(str(v) for vs in self.vars for v in vs)}"
                f"{f' ∈ {self.sub_exprs[0]}' if self.sub_exprs else ''}"
                f"{signature}")


class AQuantification(Expression):
    """ASTNode representing a quantified formula

    Args:
        annotations (Dict[str, str]):
            The set of annotations given by the expert in the IDP-Z3 program.

            ``annotations['reading']`` is the annotation
            giving the intended meaning of the expression (in English).

        q (str): either '∀' or '∃'

        quantees (List[Quantee]): list of variable declarations

        f (Expression): the formula being quantified
    """
    PRECEDENCE = 20

    def __init__(self, parent, annotations, q, quantees, f):
        self.annotations = annotations
        self.q = q
        self.quantees = quantees
        self.f = f

        self.q = '∀' if self.q == '!' else '∃' if self.q == "?" else self.q
        if self.quantees and not self.quantees[-1].sub_exprs:
            # separate untyped variables, so that they can be typed separately
            q = self.quantees.pop()
            for vars in q.vars:
                for var in vars:
                    self.quantees.append(Quantee.make(var, sort=None))

        self.sub_exprs = [self.f]
        super().__init__()

        self.type = BOOL

    @classmethod
    def make(cls,
             q: str,
             quantees: List[Quantee],
             f: Expression,
             annotations=None
             ) -> 'AQuantification':
        "make and annotate a quantified formula"
        out = cls(None, annotations, q, quantees, f)
        return out.annotate1()

    def __str1__(self):
        if self.quantees:  #TODO this is not correct in case of partial expansion
            vars = ','.join([f"{q}" for q in self.quantees])
            return f"{self.q} {vars}: {self.sub_exprs[0].str}"
        else:
            return self.sub_exprs[0].str

    def __deecopy__(self, memo):
        # also called by AAgregate
        out = Expression.__deecopy__(self, memo)
        out.quantees = [deepcopy(q, memo) for q in out.quantees]
        return out

    def collect(self, questions, all_=True, co_constraints=True):
        questions.append(self)
        if all_:
            Expression.collect(self, questions, all_, co_constraints)
            for q in self.quantees:
                q.collect(questions, all_, co_constraints)

    def collect_symbols(self, symbols=None, co_constraints=True):
        symbols = Expression.collect_symbols(self, symbols, co_constraints)
        for q in self.quantees:
            q.collect_symbols(symbols, co_constraints)
        return symbols

def FORALL(qs, expr, annotations=None):
    return AQuantification.make('∀', qs, expr, annotations)
def EXISTS(qs, expr, annotations=None):
    return AQuantification.make('∃', qs, expr, annotations)

class Operator(Expression):
    PRECEDENCE = 0  # monkey-patched
    MAP = dict()  # monkey-patched

    def __init__(self, parent, operator, sub_exprs, annotations=None):
        self.operator = operator
        self.sub_exprs = sub_exprs

        self.operator = list(map(
            lambda op: "≤" if op == "=<" else "≥" if op == ">=" else "≠" if op == "~=" else \
                "⇔" if op == "<=>" else "⇐" if op == "<=" else "⇒" if op == "=>" else \
                "∨" if op == "|" else "∧" if op == "&" else "⨯" if op == "*" else op
            , self.operator))

        super().__init__()

        self.type = BOOL if self.operator[0] in '&|∧∨⇒⇐⇔' \
               else BOOL if self.operator[0] in '=<>≤≥≠' \
               else None

    @classmethod
    def make(cls,
             ops: Union[str, List[str]],
             operands: List[Expression],
             annotations=None
             ) -> 'Operator':
        """ creates a BinaryOp
            beware: cls must be specific for ops !
        """
        if len(operands) == 0:
            if cls == AConjunction:
                return TRUE
            if cls == ADisjunction:
                return FALSE
            assert False, "Internal error"
        if len(operands) == 1:
            return operands[0]
        if isinstance(ops, str):
            ops = [ops] * (len(operands)-1)
        out = (cls)(None, ops, operands, annotations)
        if annotations:
            out.annotations = annotations
        return out.annotate1().simplify1()

    def __str1__(self):
        def parenthesis(precedence, x):
            return f"({x.str})" if type(x).PRECEDENCE <= precedence else f"{x.str}"
        precedence = type(self).PRECEDENCE
        temp = parenthesis(precedence, self.sub_exprs[0])
        for i in range(1, len(self.sub_exprs)):
            temp += f" {self.operator[i-1]} {parenthesis(precedence, self.sub_exprs[i])}"
        return temp

    def collect(self, questions, all_=True, co_constraints=True):
        if self.operator[0] in '=<>≤≥≠':
            questions.append(self)
        for e in self.sub_exprs:
            e.collect(questions, all_, co_constraints)

    def collect_nested_symbols(self, symbols, is_nested):
        return Expression.collect_nested_symbols(self, symbols,
                is_nested if self.operator[0] in ['∧','∨','⇒','⇐','⇔'] else True)


class AImplication(Operator):
    PRECEDENCE = 50

    def add_level_mapping(self, level_symbols, head, pos_justification, polarity, mode):
        sub_exprs = [self.sub_exprs[0].add_level_mapping(level_symbols, head, pos_justification, not polarity, mode),
                     self.sub_exprs[1].add_level_mapping(level_symbols, head, pos_justification, polarity, mode)]
        return self.update_exprs(sub_exprs).annotate1()

def IMPLIES(exprs, annotations=None):
    return AImplication.make('⇒', exprs, annotations)

class AEquivalence(Operator):
    PRECEDENCE = 40

    # NOTE: also used to split rules into positive implication and negative implication. Please don't change.
    def split(self):
        posimpl = IMPLIES([self.sub_exprs[0], self.sub_exprs[1]])
        negimpl = RIMPLIES(deepcopy([self.sub_exprs[0], self.sub_exprs[1]]))
        return AND([posimpl, negimpl])

    def split_equivalences(self):
        out = self.update_exprs(e.split_equivalences() for e in self.sub_exprs)
        return out.split()

def EQUIV(exprs, annotations=None):
    return AEquivalence.make('⇔', exprs, annotations)

class ARImplication(Operator):
    PRECEDENCE = 30

    def add_level_mapping(self, level_symbols, head, pos_justification, polarity, mode):
        sub_exprs = [self.sub_exprs[0].add_level_mapping(level_symbols, head, pos_justification, polarity, mode),
                     self.sub_exprs[1].add_level_mapping(level_symbols, head, pos_justification, not polarity, mode)]
        return self.update_exprs(sub_exprs).annotate1()

def RIMPLIES(exprs, annotations):
    return ARImplication.make('⇐', exprs, annotations)

class ADisjunction(Operator):
    PRECEDENCE = 60

    def __str1__(self):
        if not hasattr(self, 'enumerated'):
            return super().__str1__()
        return f"{self.sub_exprs[0].sub_exprs[0].code} in {{{self.enumerated}}}"

def OR(exprs):
    return ADisjunction.make('∨', exprs)

class AConjunction(Operator):
    PRECEDENCE = 70

def AND(exprs):
    return AConjunction.make('∧', exprs)

class AComparison(Operator):
    PRECEDENCE = 80

    def is_assignment(self):
        # f(x)=y
        return len(self.sub_exprs) == 2 and \
                self.operator in [['='], ['≠']] \
                and isinstance(self.sub_exprs[0], AppliedSymbol) \
                and all(e.value is not None
                        for e in self.sub_exprs[0].sub_exprs) \
                and self.sub_exprs[1].value is not None

def EQUALS(exprs):
    return AComparison.make('=',exprs)

class ASumMinus(Operator):
    PRECEDENCE = 90


class AMultDiv(Operator):
    PRECEDENCE = 100


class APower(Operator):
    PRECEDENCE = 110


class AUnary(Expression):
    PRECEDENCE = 120
    MAP = dict()  # monkey-patched

    def __init__(self, parent,
                 operators: List[str],
                 f: Expression):
        self.operators = operators
        self.f = f
        self.operators = ['¬' if c == '~' else c for c in self.operators]
        self.operator = self.operators[0]
        self.check(all([c == self.operator for c in self.operators]),
                   "Incorrect mix of unary operators")

        self.sub_exprs = [self.f]
        super().__init__()

    @classmethod
    def make(cls, op: str, expr: Expression) -> AUnary:
        out = AUnary(None, operators=[op], f=expr)
        return out.annotate1().simplify1()

    def __str1__(self):
        return f"{self.operator}({self.sub_exprs[0].str})"

    def add_level_mapping(self, level_symbols, head, pos_justification, polarity, mode):
        sub_exprs = (e.add_level_mapping(level_symbols, head,
                                         pos_justification,
                                         not polarity
                                         if self.operator == '¬' else polarity,
                                         mode)
                     for e in self.sub_exprs)
        return self.update_exprs(sub_exprs).annotate1()

def NOT(expr):
    return AUnary.make('¬', expr)

class AAggregate(Expression):
    PRECEDENCE = 130

    def __init__(self, parent,
                 aggtype: str,
                 quantees: List[Quantee],
                 f: Expression):
        self.aggtype = aggtype
        self.quantees = quantees
        self.f = f

        self.aggtype = "#" if self.aggtype == "card" else self.aggtype
        self.sub_exprs = [self.f]  # later: expressions to be summed
        self.annotated = False  # cannot test q_vars, because aggregate may not have quantee
        self.q = ''
        super().__init__()

    def __str1__(self):
        if not self.annotated:
            vars = ",".join([f"{q}" for q in self.quantees])
            if self.aggtype in ["sum", "min", "max"]:
                out = (f"{self.aggtype}(lambda {vars} : "
                        f"{self.sub_exprs[0].str}"
                        f")" )
            else:
                out = (f"{self.aggtype}{{{vars} : "
                       f"{self.sub_exprs[0].str}"
                       f"}}")
        else:
            out = (f"{self.aggtype}{{"
                   f"{','.join(e.str for e in self.sub_exprs)}"
                   f"}}")
        return out

    def __deepcopy__(self, memo):
        return super().__deepcopy__(memo)

    def collect(self, questions, all_=True, co_constraints=True):
        if all_ or len(self.quantees) == 0:
            Expression.collect(self, questions, all_, co_constraints)
            for q in self.quantees:
                q.collect(questions, all_, co_constraints)

    def collect_symbols(self, symbols=None, co_constraints=True):
        return AQuantification.collect_symbols(self, symbols, co_constraints)

    def collect_nested_symbols(self, symbols, is_nested):
        return Expression.collect_nested_symbols(self, symbols, True)


class AppliedSymbol(Expression):
    """Represents a symbol applied to arguments

    Args:
        symbol (SymbolExpr): the symbol to be applied to arguments

        is_enumerated (string): '' or 'is enumerated' or 'is not enumerated'

        is_enumeration (string): '' or 'in' or 'not in'

        in_enumeration (Enumeration): the enumeration following 'in'

        decl (Declaration): the declaration of the symbol, if known

        in_head (Bool): True if the AppliedSymbol occurs in the head of a rule
    """
    PRECEDENCE = 200

    def __init__(self, parent,
                 symbol,
                 sub_exprs,
                 annotations=None,
                 is_enumerated='',
                 is_enumeration='',
                 in_enumeration=''):
        self.annotations = annotations
        self.symbol = symbol
        self.sub_exprs = sub_exprs
        self.is_enumerated = is_enumerated
        self.is_enumeration = is_enumeration
        if self.is_enumeration == '∉':
            self.is_enumeration = 'not'
        self.in_enumeration = in_enumeration

        super().__init__()

        self.decl = None
        self.in_head = False

    @classmethod
    def make(cls,
             symbol: Symbol,
             args: List[Expression],
             **kwargs
             ) -> AppliedSymbol:
        out = cls(None, symbol, args, **kwargs)
        out.sub_exprs = args
        # annotate
        out.decl = symbol.decl
        return out.annotate1()

    @classmethod
    def construct(cls, constructor, args):
        out= cls.make(SYMBOL(constructor.name), args)
        out.decl = constructor
        out.variables = {}
        return out

    def __str1__(self):
        out = f"{self.symbol}({', '.join([x.str for x in self.sub_exprs])})"
        if self.in_enumeration:
            enum = f"{', '.join(str(e) for e in self.in_enumeration.tuples)}"
        return (f"{out}"
                f"{ ' '+self.is_enumerated if self.is_enumerated else ''}"
                f"{ f' {self.is_enumeration} {{{enum}}}' if self.in_enumeration else ''}")

    def __deepcopy__(self, memo):
        out = super().__deepcopy__(memo)
        out.symbol = deepcopy(out.symbol)
        return out

    def collect(self, questions, all_=True, co_constraints=True):
        if self.decl and self.decl.name not in RESERVED_SYMBOLS:
            questions.append(self)
            if self.is_enumerated or self.in_enumeration:
                app = AppliedSymbol.make(self.symbol, self.sub_exprs)
                questions.append(app)
        self.symbol.collect(questions, all_, co_constraints)
        for e in self.sub_exprs:
            e.collect(questions, all_, co_constraints)
        if co_constraints and self.co_constraint is not None:
            self.co_constraint.collect(questions, all_, co_constraints)

    def collect_symbols(self, symbols=None, co_constraints=True):
        symbols = Expression.collect_symbols(self, symbols, co_constraints)
        self.symbol.collect_symbols(symbols, co_constraints)
        return symbols

    def collect_nested_symbols(self, symbols, is_nested):
        if is_nested and (hasattr(self, 'decl') and self.decl
            and type(self.decl) != Constructor
            and not self.decl.name in RESERVED_SYMBOLS):
            symbols.add(self.decl)
        for e in self.sub_exprs:
            e.collect_nested_symbols(symbols, True)
        return symbols

    def has_decision(self):
        self.check(self.decl.block is not None, "Internal error")
        return not self.decl.block.name == 'environment' \
            or any(e.has_decision() for e in self.sub_exprs)

    def type_inference(self):
        if self.symbol.decl:
            self.check(self.symbol.decl.arity == len(self.sub_exprs),
                f"Incorrect number of arguments in {self}: "
                f"should be {self.symbol.decl.arity}")
        try:
            out = {}
            for i, e in enumerate(self.sub_exprs):
                if self.decl and isinstance(e, Variable):
                    out[e.name] = self.decl.sorts[i]
                else:
                    out.update(e.type_inference())
            return out
        except AttributeError as e:
            #
            if "object has no attribute 'sorts'" in str(e):
                msg = f"Unexpected arity for symbol {self}"
            else:
                msg = f"Unknown error for symbol {self}"
            self.check(False, msg)

    def is_reified(self):
        return (self.in_enumeration or self.is_enumerated
                or not all(e.value is not None for e in self.sub_exprs))

    def reified(self, problem: Theory):
        return ( super().reified(problem) if self.is_reified() else
                 self.translate(problem) )

    def generate_constructors(self, constructors: dict):
        symbol = self.symbol.sub_exprs[0]
        if hasattr(symbol, 'name') and symbol.name in ['unit', 'heading']:
            constructor = CONSTRUCTOR(self.sub_exprs[0].name)
            constructors[symbol.name].append(constructor)

    def add_level_mapping(self, level_symbols, head, pos_justification, polarity, mode):
        assert head.symbol.decl in level_symbols, \
               f"Internal error in level mapping: {self}"
        if self.symbol.decl not in level_symbols or self.in_head:
            return self
        else:
            if mode == Semantics.WELLFOUNDED:
                op = ('>' if pos_justification else '≥') \
                    if polarity else ('≤' if pos_justification else '<')
            elif mode == Semantics.KRIPKEKLEENE:
                op = '>' if polarity else '≤'
            else:
                assert mode == Semantics.COINDUCTION, \
                        f"Internal error: {mode}"
                op = ('≥' if pos_justification else '>') \
                    if polarity else ('<' if pos_justification else '≤')
            comp = AComparison.make(op, [
                AppliedSymbol.make(level_symbols[head.symbol.decl], head.sub_exprs),
                AppliedSymbol.make(level_symbols[self.symbol.decl], self.sub_exprs)
            ])
            if polarity:
                return AND([comp, self])
            else:
                return OR([comp, self])


class SymbolExpr(Expression):
    def __init__(self, parent, s, eval=''):
        self.eval = eval
        self.sub_exprs = [s]
        self.decl = self.sub_exprs[0].decl if not self.eval else None
        super().__init__()

    def __str1__(self):
        return (f"$({self.sub_exprs[0]})" if self.eval else
                f"{self.sub_exprs[0]}")

    def is_intentional(self):
        return self.eval

class UnappliedSymbol(Expression):
    """The result of parsing a symbol not applied to arguments.
    Can be a constructor or a quantified variable.

    Variables are converted to Variable() by annotate().
    """
    PRECEDENCE = 200

    def __init__(self, parent, s):
        self.s = s
        self.name = self.s.name

        Expression.__init__(self)

        self.sub_exprs = []
        self.decl = None
        self.is_enumerated = None
        self.is_enumeration = None
        self.in_enumeration = None
        self.value = self

    @classmethod
    def construct(cls, constructor: Constructor):
        """Create an UnappliedSymbol from a constructor
        """
        out = (cls)(None, s=SYMBOL(constructor.name))
        out.decl = constructor
        out.variables = {}
        return out

    def __str1__(self): return self.name


TRUEC = CONSTRUCTOR('true')
FALSEC = CONSTRUCTOR('false')

TRUE = UnappliedSymbol.construct(TRUEC)
FALSE = UnappliedSymbol.construct(FALSEC)

class Variable(Expression):
    """AST node for a variable in a quantification or aggregate

    Args:
        name (str): name of the variable

        sort (Optional[Union[Type, Symbol]]): sort of the variable, if known
    """
    PRECEDENCE = 200

    def __init__(self, parent,
                 name:str,
                 sort: Optional[Union[Type, Symbol]]=None):
        self.name = name
        sort = sort
        self.sort = sort
        assert sort is None or isinstance(sort, Type) or isinstance(sort, Symbol), \
            f"Internal error: {self}"

        super().__init__()

        self.type = sort.decl.name if sort and sort.decl else ''
        self.sub_exprs = []
        self.variables = set([self.name])

    def __str1__(self): return self.name

    def __deepcopy__(self, memo):
        return self

    def annotate1(self): return self

def VARIABLE(name: str, sort: Union[Type, Symbol]):
    return Variable(None, name, sort)

class Number(Expression):
    PRECEDENCE = 200

    def __init__(self, **kwargs):
        self.number = kwargs.pop('number')

        super().__init__()

        self.sub_exprs = []
        self.variables = set()
        self.value = self

        ops = self.number.split("/")
        if len(ops) == 2:  # possible with str_to_IDP on Z3 value
            self.py_value = Fraction(self.number)
            self.type = REAL
        elif '.' in self.number:
            self.py_value = Fraction(self.number if not self.number.endswith('?') else
                                     self.number[:-1])
            self.type = REAL
        else:
            self.py_value = int(self.number)
            self.type = INT

    def __str__(self): return self.number

    def real(self):
        """converts the INT number to REAL"""
        self.check(self.type in [INT, REAL], f"Can't convert {self} to {REAL}")
        return Number(number=str(float(self.py_value)))


ZERO = Number(number='0')
ONE = Number(number='1')


class Date(Expression):
    PRECEDENCE = 200

    def __init__(self, **kwargs):
        self.iso = kwargs.pop('iso')

        dt = (date.today() if self.iso == '#TODAY' else
                     date.fromisoformat(self.iso[1:]))
        if 'y' in kwargs:
            y = int(kwargs.pop('y'))
            m = int(kwargs.pop('m'))
            d = int(kwargs.pop('d'))
            dt = dt + relativedelta(years=y, months=m, days=d)
        self.date = dt

        super().__init__()

        self.sub_exprs = []
        self.variables = set()
        self.value = self

        self.py_value = int(self.date.toordinal())
        self.type = DATE

    @classmethod
    def make(cls, value: int) -> Date:
        return cls(iso=f"#{date.fromordinal(value).isoformat()}")

    def __str__(self): return f"#{self.date.isoformat()}"


class Brackets(Expression):
    PRECEDENCE = 200

    def __init__(self, **kwargs):
        self.f = kwargs.pop('f')
        self.annotations = kwargs.pop('annotations')
        if not self.annotations:
            self.annotations = {'reading': self.f.annotations['reading']}
        self.sub_exprs = [self.f]

        super().__init__()


    # don't @use_value, to have parenthesis
    def __str__(self): return f"({self.sub_exprs[0].str})"
    def __str1__(self): return str(self)

