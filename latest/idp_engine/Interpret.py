# cython: binding=True

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

Methods to ground / interpret a theory in a data structure

* expand quantifiers
* replace symbols interpreted in the structure by their interpretation

This module also includes methods to:

* substitute a node by another in an AST tree
* instantiate an expresion, i.e. replace a variable by a value

This module monkey-patches the ASTNode class and sub-classes.

( see docs/zettlr/Substitute.md )

"""
from __future__ import annotations

from copy import copy, deepcopy
from itertools import product
from typing import Dict, List, Callable

from .Assignments import Status as S
from .Parse import (Import, TypeDeclaration, SymbolDeclaration,
    SymbolInterpretation, FunctionEnum, Enumeration, TupleIDP, ConstructedFrom,
    Definition, ConstructedFrom, Ranges)
from .Expression import (Symbol, SYMBOL, AIfExpr, IF, SymbolExpr, Expression, Constructor,
    AQuantification, Type, FORALL, IMPLIES, AND, AAggregate,
    NOT, EQUALS, AppliedSymbol, UnappliedSymbol, Quantee, TYPE,
    Variable, VARIABLE, TRUE, FALSE, Number, Extension)
from .Theory import Theory
from .utils import (BOOL, RESERVED_SYMBOLS, CONCEPT, OrderedSet, DEFAULT,
                    GOAL_SYMBOL, EXPAND)


# class Import  ###########################################################

def interpret(self, problem):
    pass
Import.interpret = interpret


# class TypeDeclaration  ###########################################################

def interpret(self, problem):
    interpretation = problem.interpretations.get(self.name, None)
    if self.name in [BOOL, CONCEPT]:
        self.translate(problem)
        ranges = [c.interpret(problem).range for c in self.constructors]
        ext = ([[t] for r in ranges for t in r], None)
        problem.extensions[self.name] = ext
    else:
        enum = interpretation.enumeration.interpret(problem)
        self.interpretation = interpretation
        self.constructors = enum.constructors
        self.translate(problem)

        if self.constructors is not None:
            for c in self.constructors:
                c.interpret(problem)

        # update problem.extensions
        ext = enum.extensionE(problem.interpretations, problem.extensions)
        problem.extensions[self.name] = ext

        # needed ?
        # if (isinstance(self.interpretation.enumeration, Ranges)
        # and self.interpretation.enumeration.tuples):
        #     # add condition that the interpretation is total over the infinite domain
        #     # ! x in N: type(x) <=> enum.contains(x)
        #     t = TYPE(self.type)  # INT, REAL or DATE
        #     t.decl, t.type = self, self.type
        #     var = VARIABLE(f"${self.name}!0$",t)
        #     q_vars = { f"${self.name}!0$": var}
        #     quantees = [Quantee.make(var, subtype=t)]
        #     expr1 = AppliedSymbol.make(SYMBOL(self.name), [var])
        #     expr1.decl = self
        #     expr2 = enum.contains(list(q_vars.values()), True)
        #     expr = EQUALS([expr1, expr2])
        #     constraint = FORALL(quantees, expr)
        #     constraint.annotations['reading'] = f"Enumeration of {self.name} should cover its domain"
        #     problem.constraints.append(constraint)
TypeDeclaration.interpret = interpret


# class SymbolDeclaration  ###########################################################

def interpret(self, problem):
    assert all(isinstance(s, Type) for s in self.sorts), 'internal error'

    symbol = SYMBOL(self.name)
    symbol.decl = self
    symbol.type = symbol.decl.type

    # determine the extension, i.e., (superset, filter)
    extensions = [s.extension(problem.interpretations, problem.extensions)
                for s in self.sorts]
    if any(e[0] is None for e in extensions):
        superset = None
    else:
        superset = list(product(*([ee[0] for ee in e[0]] for e in extensions)))

    filters = [e[1] for e in extensions]
    def filter(args):
        out = AND([f([deepcopy(t)]) if f is not None else TRUE
                    for f, t in zip(filters, args)])
        if self.out.decl.name == BOOL:
            out = AND([out, deepcopy(AppliedSymbol.make(symbol, args))])
        return out

    if self.out.decl.name == BOOL:
        problem.extensions[self.name] = (superset, filter)

    (range, _) = self.out.extension(problem.interpretations, problem.extensions)
    if range is None:
        self.range = []
    else:
        self.range = [e[0] for e in range]

    # create instances + empty assignment
    self.instances = {}
    if self.name not in RESERVED_SYMBOLS and superset:
        for args in superset:
            expr = AppliedSymbol.make(symbol, args)
            expr.annotate(self.voc, {})
            self.instances[expr.code] = expr
            problem.assignments.assert__(expr, None, S.UNKNOWN)

    # interpret the enumeration
    if self.name in problem.interpretations and self.name != GOAL_SYMBOL:
        problem.interpretations[self.name].interpret(problem)

    # create type constraints
    if self.out.decl.name != BOOL:
        for expr in self.instances.values():
            # add type constraints to problem.constraints
            # ! (x,y) in domain: range(f(x,y))
            range_condition = self.out.has_element(deepcopy(expr),
                                problem.interpretations, problem.extensions)
            range_condition = range_condition.interpret(problem)
            constraint = IMPLIES([filter(expr.sub_exprs), range_condition])
            constraint.block = self.block
            constraint.is_type_constraint_for = self.name
            constraint.annotations['reading'] = f"Possible values for {expr}"
            problem.constraints.append(constraint)
SymbolDeclaration.interpret = interpret


# class Definition  ###########################################################

def interpret(self, problem):
    """updates problem.def_constraints, by expanding the definitions

    Args:
        problem (Theory):
            containts the enumerations for the expansion; is updated with the expanded definitions
    """
    self.cache = {}  # reset the cache
    self.instantiables = self.get_instantiables(problem.interpretations, problem.extensions)
    self.add_def_constraints(self.instantiables, problem, problem.def_constraints)
Definition.interpret = interpret

def add_def_constraints(self, instantiables, problem, result):
    """result is updated with the constraints for this definition.

    The `instantiables` (of the definition) are expanded in `problem`.

    Args:
        instantiables (Dict[SymbolDeclaration, List[Expression]]):
            the constraints without the quantification

        problem (Theory):
            contains the structure for the expansion/interpretation of the constraints

        result (Dict[SymbolDeclaration, Definition, List[Expression]]):
            a mapping from (Symbol, Definition) to the list of constraints
    """
    for decl, bodies in instantiables.items():
        quantees = self.canonicals[decl][0].quantees  # take quantee from 1st renamed rule
        expr = [FORALL(quantees, e, e.annotations).interpret(problem)
                for e in bodies]
        result[decl, self] = expr
Definition.add_def_constraints = add_def_constraints


# class SymbolInterpretation  ###########################################################

def interpret(self, problem):
    status = S.DEFAULT if self.block.name == DEFAULT else S.STRUCTURE
    assert not self.is_type_enumeration, "Internal error"
    if not self.name in [GOAL_SYMBOL, EXPAND]:
        decl = problem.declarations[self.name]
        # update problem.extensions
        if self.symbol.decl.out.decl.name == BOOL:  # predicate
            extension = [t.args for t in self.enumeration.tuples]
            problem.extensions[self.symbol.name] = (extension, None)

        enumeration = self.enumeration  # shorthand
        self.check(all(len(t.args) == self.symbol.decl.arity
                            + (1 if type(enumeration) == FunctionEnum else 0)
                        for t in enumeration.tuples),
            f"Incorrect arity of tuples in Enumeration of {self.symbol}.  Please check use of ',' and ';'.")

        lookup = {}
        if hasattr(decl, 'instances') and decl.instances and self.default:
            lookup = { ",".join(str(a) for a in applied.sub_exprs): self.default
                    for applied in decl.instances.values()}
        if type(enumeration) == FunctionEnum:
            lookup.update( (','.join(str(a) for a in t.args[:-1]), t.args[-1])
                        for t in enumeration.sorted_tuples)
        else:
            lookup.update( (t.code, TRUE)
                            for t in enumeration.sorted_tuples)
        enumeration.lookup = lookup

        # update problem.assignments with data from enumeration
        for t in enumeration.tuples:

            # check that the values are in the range
            if type(self.enumeration) == FunctionEnum:
                args, value = t.args[:-1], t.args[-1]
                condition = decl.has_in_range(value,
                            problem.interpretations, problem.extensions)
                self.check(not condition.same_as(FALSE),
                           f"{value} is not in the range of {self.symbol.name}")
                if not condition.same_as(TRUE):
                    problem.constraints.append(condition)
            else:
                args, value = t.args, TRUE

            # check that the arguments are in the domain
            a = (str(args) if 1<len(args) else
                    str(args[0]) if len(args)==1 else
                    "()")
            self.check(len(args) == decl.arity,
                       f"Incorrect arity of {a} for {self.name}")
            condition = decl.has_in_domain(args,
                            problem.interpretations, problem.extensions)
            self.check(not condition.same_as(FALSE),
                       f"{a} is not in the domain of {self.symbol.name}")
            if not condition.same_as(TRUE):
                problem.constraints.append(condition)

            # check duplicates
            expr = AppliedSymbol.make(self.symbol, args)
            self.check(expr.code not in problem.assignments
                or problem.assignments[expr.code].status == S.UNKNOWN,
                f"Duplicate entry in structure for '{self.name}': {str(expr)}")

            # add to problem.assignments
            e = problem.assignments.assert__(expr, value, status)
            if (status == S.DEFAULT  # for proper display in IC
                and type(self.enumeration) == FunctionEnum):
                problem.assignments.assert__(e.formula(), TRUE, status)

        if self.default is not None:
            # fill the default value in problem.assignments
            for code, expr in decl.instances.items():
                if (code not in problem.assignments
                    or problem.assignments[code].status != status):
                    e = problem.assignments.assert__(expr, self.default, status)
                    if (status == S.DEFAULT  # for proper display in IC
                        and type(self.enumeration) == FunctionEnum
                        and self.default.type != BOOL):
                        problem.assignments.assert__(e.formula(), TRUE, status)

            if isinstance(enumeration, Ranges) and enumeration.tuples and self.sign == '≜':
                # add condition that the interpretation is total over the infinite domain (#235)
                # ! x in N: type(x) <=> enum.contains(x)
                t = TYPE(enumeration.type)  # INT, REAL or DATE
                t.decl, t.type = problem.declarations[enumeration.type], enumeration.type
                var = VARIABLE(f"${self.name}!0$", t)
                q_vars = { f"${self.name}!0$": var}
                quantees = [Quantee.make(var, subtype=t)]
                expr1 = AppliedSymbol.make(SYMBOL(self.name), [var])
                expr1.decl = self.symbol.decl
                expr2 = enumeration.contains(list(q_vars.values()), True)
                expr = EQUALS([expr1, expr2])
                constraint = FORALL(quantees, expr)
                constraint.annotations['reading'] = f"Enumeration of {self.name} should cover its domain"
                problem.constraints.append(constraint)
        elif self.sign == '≜':
            # add condition that the interpretation is total over the domain
            # ! x in dom(f): enum.contains(x)
            q_vars = { f"${sort.decl.name}!{str(i)}$":
                       VARIABLE(f"${sort.decl.name}!{str(i)}$", sort)
                       for i, sort in enumerate(decl.sorts)}
            quantees = [Quantee.make(v, sort=v.sort) for v in q_vars.values()]
            expr = self.enumeration.contains(list(q_vars.values()), True)
            constraint = FORALL(quantees, expr).interpret(problem)
            constraint.annotations['reading'] = f"Enumeration of {self.name} should cover its domain"
            problem.constraints.append(constraint)
SymbolInterpretation.interpret = interpret


# class Enumeration  ###########################################################

def interpret(self, problem):
    return self
Enumeration.interpret = interpret


# class ConstructedFrom  ###########################################################

def interpret(self, problem):
    self.tuples = OrderedSet()
    for c in self.constructors:
        c.interpret(problem)
        if c.range is None:
            self.tuples = None
            return self
        self.tuples.extend([TupleIDP(args=[e]) for e in c.range])
    return self
ConstructedFrom.interpret = interpret


# class Constructor  ###########################################################

def interpret(self, problem):
    assert all(isinstance(s.decl.out, Type) for s in self.sorts), 'internal error'
    if not self.sorts:
        self.range = [UnappliedSymbol.construct(self)]
    else:
        extensions = [s.decl.out.extension(problem.interpretations, problem.extensions)
                      for s in self.sorts]
        if any(e[0] is None for e in extensions):
            self.range = None
        else:
            self.check(all(e[1] is None for e in extensions),  # no filter in the extension
                       f"Type signature of constructor {self.name} must have a given interpretation")
            self.range = [AppliedSymbol.construct(self, es)
                          for es in product(*[[ee[0] for ee in e[0]] for e in extensions])]
    return self
Constructor.interpret = interpret


# class Expression  ###########################################################

def interpret(self, problem) -> Expression:
    """ uses information in the problem and its vocabulary to:
    - expand quantifiers in the expression
    - simplify the expression using known assignments and enumerations
    - instantiate definitions

    Args:
        problem (Theory): the Theory to apply

    Returns:
        Expression: the resulting expression
    """
    if self.is_type_constraint_for:  # do not interpret typeConstraints
        return self
    out = self.update_exprs(e.interpret(problem) for e in self.sub_exprs)
    return out
Expression.interpret = interpret


# @log  # decorator patched in by tests/main.py
def substitute(self, e0, e1, assignments, tag=None):
    """ recursively substitute e0 by e1 in self (e0 is not a Variable)

    if tag is present, updates assignments with symbolic propagation of co-constraints.

    implementation for everything but AppliedSymbol, UnappliedSymbol and
    Fresh_variable
    """
    assert not isinstance(e0, Variable) or isinstance(e1, Variable), \
               f"Internal error in substitute {e0} by {e1}" # should use instantiate instead
    assert self.co_constraint is None,  \
               f"Internal error in substitue: {self.co_constraint}" # see AppliedSymbol instead

    # similar code in AppliedSymbol !
    if self.code == e0.code:
        if self.code == e1.code:
            return self  # to avoid infinite loops
        return self._change(value=e1)  # e1 is UnappliedSymbol or Number
    else:
        # will update self.simpler
        out = self.update_exprs(e.substitute(e0, e1, assignments, tag)
                                for e in self.sub_exprs)
        return out
Expression.substitute = substitute


def instantiate(self, e0, e1, problem=None):
    """Recursively substitute Variable in e0 by e1 in a copy of self.
    Update .variables.
    """
    assert all(type(e) == Variable for e in e0), \
           f"Internal error: instantiate {e0}"
    if self.value:
        return self
    out = copy(self)  # shallow copy !
    out.annotations = copy(out.annotations)
    out.variables = copy(out.variables)
    return out.instantiate1(e0, e1, problem)
Expression.instantiate = instantiate

def instantiate1(self, e0, e1, problem=None):
    """Recursively substitute Variable in e0 by e1 in self.

    Interpret appliedSymbols immediately if grounded (and not occurring in head of definition).
    Update .variables.
    """
    # instantiate expressions, with simplification
    out = self.update_exprs(e.instantiate(e0, e1, problem)
                            for e in self.sub_exprs)

    if out.value is not None:  # replace by new value
        out = out.value
    else:
        self.check(len(e0) == len(e1),
                   f"Incorrect arity: {e0}, {e1}")
        for o, n in zip(e0, e1):
            if o.name in out.variables:
                out.variables.discard(o.name)
                if type(n) == Variable:
                    out.variables.add(n.name)
            out.code = str(out)
    out.annotations['reading'] = out.code
    return out
Expression.instantiate1 = instantiate1


# class Symbol ###########################################################

def instantiate(self, e0, e1, problem=None):
    return self
Symbol.instantiate = instantiate


# class Type ###########################################################

def extension(self, interpretations: Dict[str, SymbolInterpretation],
              extensions: Dict[str, Extension]
              ) -> Extension:
    """returns the extension of a Type, given some interpretations.

    Normally, the extension is already in `extensions`.
    However, for Concept[T->T], an additional filtering is applied.

    Args:
        interpretations (Dict[str, SymbolInterpretation]):
        the known interpretations of types and symbols

    Returns:
        Extension: a superset of the extension of self,
        and a function that, given arguments, returns an Expression that says
        whether the arguments are in the extension of self
    """
    if self.code not in extensions:
        self.check(self.name == CONCEPT, "internal error")
        assert self.out, "internal error"  # Concept[T->T]
        out = [v for v in extensions[CONCEPT][0]
                if v[0].decl.symbol.decl.arity == len(self.ins)
                and isinstance(v[0].decl.symbol.decl, SymbolDeclaration)
                and v[0].decl.symbol.decl.out == self.out
                and len(v[0].decl.symbol.decl.sorts) == len(self.ins)
                and all(s == q
                        for s, q in zip(v[0].decl.symbol.decl.sorts,
                                        self.ins))]
        extensions[self.code] = (out, None)
    return extensions[self.code]
Type.extension = extension

# Class AQuantification  ######################################################

def _add_filter(q: str, expr: Expression, filter: Callable, args: List[Expression],
                theory: Theory) -> Expression:
    """add `filter(args)` to `expr` quantified by `q`

    Example: `_add_filter('∀', TRUE, filter, [1], theory)` returns `filter([1]) => TRUE`

    Args:
        q: the type of quantification
        expr: the quantified expression
        filter: a function that returns an Expression for some arguments
        args:the arguments to be applied to filter

    Returns:
        Expression: `expr` extended with appropriate filter
    """
    if filter:  # adds `filter(val) =>` in front of expression
        applied = filter(args).interpret(theory)
        if q == '∀':
            out = IMPLIES([applied, expr])
        elif q == '∃':
            out = AND([applied, expr])
        else:  # aggregate
            if isinstance(expr, AIfExpr):  # cardinality
                # if a then b else 0 -> if (applied & a) then b else 0
                arg1 = AND([applied, expr.sub_exprs[0]])
                out = IF(arg1, expr.sub_exprs[1], expr.sub_exprs[2])
            else:  # sum
                out = IF(applied, expr, Number(number="0"))
        return out
    return expr

def interpret(self, problem):
    """apply information in the problem and its vocabulary

    Args:
        problem (Theory): the problem to be applied

    Returns:
        Expression: the expanded quantifier expression
    """
    # This method is called by AAggregate.interpret !
    if not self.quantees:
        return Expression.interpret(self, problem)
    self.check(len(self.sub_exprs) == 1, "Internal error")

    # type inference
    inferred = self.sub_exprs[0].type_inference()
    for q in self.quantees:
        if not q.sub_exprs:
            assert len(q.vars) == 1 and q.arity == 1, \
                   f"Internal error: interpret {q}"
            var = q.vars[0][0]
            self.check(var.name in inferred,
                        f"can't infer type of {var.name}")
            var.sort = inferred[var.name]
            q.sub_exprs = [inferred[var.name]]

    forms = self.sub_exprs
    new_quantees, instantiated = [], False
    for q in self.quantees:
        domain = q.sub_exprs[0]

        superset, filter = None, None
        if isinstance(domain, Type):  # quantification over type / Concepts
            (superset, filter) = domain.extension(problem.interpretations,
                                        problem.extensions)
        elif isinstance(domain, SymbolExpr):  # SymbolExpr (e.g. $(`Color))
            self.check(domain.decl.out.type == BOOL,
                        f"{domain} is not a type or predicate")
            assert domain.decl.name in problem.extensions, "internal error"
            (superset, filter) = problem.extensions[domain.decl.name]
        else:
            self.check(False, f"Can't resolve the domain of {str(q.vars)}")

        if superset is None:
            new_quantees.append(q)
            for vars in q.vars:
                forms = [_add_filter(self.q, f, filter, vars, problem) for f in forms]
        else:
            for vars in q.vars:
                self.check(domain.decl.arity == len(vars),
                            f"Incorrect arity of {domain}")
                out = []
                for f in forms:
                    for val in superset:
                        new_f = f.instantiate(vars, val, problem)
                        instantiated = True
                        out.append(_add_filter(self.q, new_f, filter, val, problem))
                forms = out

    if not instantiated:
        forms = [f.interpret(problem) if problem else f for f in forms]
    self.quantees = new_quantees
    return self.update_exprs(forms)
AQuantification.interpret = interpret


def instantiate1(self, e0, e1, problem=None):
    out = Expression.instantiate1(self, e0, e1, problem)  # updates .variables
    for q in self.quantees: # for !x in $(output_domain(s,1))
        if q.sub_exprs:
            q.sub_exprs[0] = q.sub_exprs[0].instantiate(e0, e1, problem)
    if problem and not self.variables:  # expand nested quantifier if no variables left
        out = out.interpret(problem)
    return out
AQuantification.instantiate1 = instantiate1


# Class AAggregate  ######################################################

def interpret(self, problem):
    assert self.annotated, f"Internal error in interpret"
    return AQuantification.interpret(self, problem)
AAggregate.interpret = interpret

AAggregate.instantiate1 = instantiate1  # from AQuantification


# Class AppliedSymbol  ##############################################

def interpret(self, problem):
    self.symbol = self.symbol.interpret(problem)
    sub_exprs = [e.interpret(problem) for e in self.sub_exprs]
    value, simpler, co_constraint = None, None, None
    if self.decl:
        if self.is_enumerated:
            assert self.decl.type != BOOL, \
                f"Can't use 'is enumerated' with predicate {self.decl.name}."
            if self.decl.name in problem.interpretations:
                interpretation = problem.interpretations[self.decl.name]
                if interpretation.default is not None:
                    simpler = TRUE
                else:
                    simpler = interpretation.enumeration.contains(sub_exprs, True,
                        interpretations=problem.interpretations, extensions=problem.extensions)
                if 'not' in self.is_enumerated:
                    simpler = NOT(simpler)
                simpler.annotations = self.annotations
        elif self.in_enumeration:
            # re-create original Applied Symbol
            core = deepcopy(AppliedSymbol.make(self.symbol, sub_exprs))
            simpler = self.in_enumeration.contains([core], False,
                        interpretations=problem.interpretations, extensions=problem.extensions)
            if 'not' in self.is_enumeration:
                simpler = NOT(simpler)
            simpler.annotations = self.annotations
        elif (self.decl.name in problem.interpretations
            # and any(s.decl.name == CONCEPT for s in self.decl.sorts)
            and all(a.value is not None for a in sub_exprs)):
            # apply enumeration of predicate over symbols to allow simplification
            # do not do it otherwise, for performance reasons
            interpretation = problem.interpretations[self.decl.name]
            if interpretation.block.name != DEFAULT:
                f = interpretation.interpret_application
                value = f(0, self, sub_exprs)
        elif self.decl.name in problem.interpretations:
            self.decl.needs_interpretation = True
        if not self.in_head and not self.variables:
            # instantiate definition (for relevance)
            inst = [defin.instantiate_definition(self.decl, sub_exprs, problem)
                    for defin in problem.definitions]
            inst = [x for x in inst if x]
            if inst:
                co_constraint = AND(inst)
        out = (value if value else
               self._change(sub_exprs=sub_exprs, simpler=simpler,
                        co_constraint=co_constraint))
        return out
    else:
        return self
AppliedSymbol.interpret = interpret


# @log_calls  # decorator patched in by tests/main.py
def substitute(self, e0, e1, assignments, tag=None):
    """ recursively substitute e0 by e1 in self """

    assert not isinstance(e0, Variable) or isinstance(e1, Variable), \
        f"should use 'instantiate instead of 'substitute for {e0}->{e1}"

    new_branch = None
    if self.co_constraint is not None:
        new_branch = self.co_constraint.substitute(e0, e1, assignments, tag)
        if tag is not None:
            new_branch.symbolic_propagate(assignments, tag)

    if self.code == e0.code:
        return self._change(value=e1, co_constraint=new_branch)
    elif self.simpler is not None:  # has an interpretation
        assert self.co_constraint is None, \
               f"Internal error in substitute: {self}"
        simpler = self.simpler.substitute(e0, e1, assignments, tag)
        return self._change(simpler=simpler)
    else:
        sub_exprs = [e.substitute(e0, e1, assignments, tag)
                     for e in self.sub_exprs]  # no simplification here
        return self._change(sub_exprs=sub_exprs, co_constraint=new_branch)
AppliedSymbol .substitute = substitute

def instantiate1(self, e0, e1, problem=None):
    out = Expression.instantiate1(self, e0, e1, problem)  # update .variables
    if type(out) == AppliedSymbol:  # might be a number after instantiation
        if type(out.symbol) == SymbolExpr and out.symbol.is_intentional():  # $(x)()
            out.symbol = out.symbol.instantiate(e0, e1, problem)
            if type(out.symbol) == Symbol:  # found $(x)
                self.check(len(out.sub_exprs) == len(out.symbol.decl.sorts),
                            f"Incorrect arity for {out.code}")
                kwargs = ({'is_enumerated': out.is_enumerated} if out.is_enumerated else
                          {'in_enumeration': out.in_enumeration} if out.in_enumeration else
                          {})
                out = AppliedSymbol.make(out.symbol, out.sub_exprs, **kwargs)
                out.original = self
        if out.co_constraint is not None:
            out.co_constraint.instantiate(e0, e1, problem)
        if problem and not self.variables:
            return out.interpret(problem)
    return out
AppliedSymbol .instantiate1 = instantiate1


# Class Variable  #######################################################

def interpret(self, problem):
    return self
Variable.interpret = interpret

# @log  # decorator patched in by tests/main.py
def substitute(self, e0, e1, assignments, tag=None):
    if self.sort:
        self.sort = self.sort.substitute(e0,e1, assignments, tag)
    return e1 if self.code == e0.code else self
Variable.substitute = substitute

def instantiate1(self, e0, e1, problem=None):
    if self.sort:
        self.sort = self.sort.instantiate(e0, e1, problem)
    self.check(len(e0) == len(e1),
               f"Incorrect arity: {e0}, {e1}")
    for o, n in zip(e0, e1):
        if self.code == o.code:
            return n
    return self
Variable.instantiate1 = instantiate1



Done = True
