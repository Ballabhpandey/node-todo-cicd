#
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

Class to represent a collection of theory and structure blocks.

"""
from __future__ import annotations

import time
from copy import copy, deepcopy
from enum import Enum, auto
from itertools import chain
import logging
import math
from typing import Any, Dict, Iterator, List, Optional, Tuple, Union
from z3 import (Context, BoolRef, ExprRef, Solver, sat, unsat, Optimize, Not, And, Or, Implies,
                is_and, BoolVal, get_param)

from .Assignments import Status as S, Assignment, Assignments
from .Lift import transform
from .Expression import (TRUE, Expression, FALSE, AppliedSymbol, UnappliedSymbol, Constructor,
                         EQUALS, NOT, Extension, Number, AQuantification, AAggregate)
from .Parse import (IDP, TypeDeclaration, Declaration, SymbolDeclaration, SYMBOL,
                    TheoryBlock, Structure, Definition, str_to_IDP,
                    SymbolInterpretation, Ranges, RangeElement, TupleIDP, Enumeration)
from .Simplify import join_set_conditions
from .utils import (OrderedSet, NEWL, BOOL, INT, REAL, DATE, IDPZ3Error,
                    RESERVED_SYMBOLS, CONCEPT, GOAL_SYMBOL, RELEVANT, NOT_SATISFIABLE)

class Propagation(Enum):
    """Describe propagation method    """
    DEFAULT = auto()  # checks each question to see if it can have only 1 value
    BATCH = auto()  # finds a list of questions that has only 1 value
    Z3 = auto()  # use Z3's consequences API (incomplete propagation)


class Theory(object):
    """A collection of theory and structure blocks.

        assignments (Assignments): the set of assignments.
            The assignments are updated by the different steps of the problem
            resolution.  Assignments include inequalities and quantified formula
            when the problem is extended
    """
    """  do not include these in the API documentation
    Attributes:
        extended (Bool): True when the truth value of inequalities
            and quantified formula is of interest (e.g. in the Interactive Consultant)

        declarations (Dict[str, Declaration]): the list of type and symbol declarations

        constraints (OrderedSet): a set of assertions.

        definitions ([Definition]): a list of definitions in this problem

        interpretations (Dict[string, SymbolInterpretation]):
            A mapping of enumerated symbols to their interpretation.

        extensions (Dict[string, Extension]):
            Extension of types and predicates

        def_constraints (Dict[SymbolDeclaration, Definition], List[Expression]):
            A mapping of defined symbol to the whole-domain constraints
            equivalent to its definition.

        _constraintz (List(ExprRef), Optional): a list of assertions, co_constraints and definitions in Z3 form

        _formula (ExprRef, optional): the Z3 formula that represents
            the problem (assertions, co_constraints, definitions and assignments).

        co_constraints (OrderedSet): the set of co_constraints in the problem.

        z3 (Dict[str, ExprRef]): mapping from string of the code to Z3 expression, to avoid recomputing it

        ctx : Z3 context

        previous_assignments (Assignment): assignment after previous full propagation

        satisfied (Bool): whether propagate found an initial model

        _slvr (Solver): stateful solver used for propagation and model expansion.
            Use self.solver to access.

        _optmz (Solver): stateful solver used for optimization.
            Use self.optimize_solver to access.

        _reified (Solver): stateful solver used for explanation and disabling laws.
            Use self.solver_reified to access.

        _optmz_reif (Solver): stateful solver used for optimizing when disabling laws.
            Use self.optimize_solver_reified to access.

        expl_reifs = (Dict[z3.BoolRef, (z3.BoolRef,Expression)]):
            dictionary storing for Z3 reification symbols (the keys) which
            Z3 constraint it represents, and what the original FO(.) expression was.
            If the original expression is `None`, the reification represents a
            fact, otherwise it represents a law. Used in the explanation
            inference and when disabling laws.

        ignored_laws = set(string): laws disabled by the user.
            The string matches Expression.code in expl_reifs.

    """
    def __init__(self,
                 *theories: Union[TheoryBlock, Structure, "Theory"],
                 extended: bool = False
                 ) -> None:
        """Creates an instance of ``Theory`` for the list of theories, e.g., ``Theory(T,S)``.

        Args:
            theories (Union[TheoryBlock, Structure, Theory]): 1 or more (data) theories.
            extended (bool, optional): use `True` when the truth value of
                inequalities and quantified formula is of interest
                (e.g. for the Interactive Consultant).
                Defaults to False.
        """

        self.extended: Optional[bool] = extended

        self.declarations: Dict[str, Declaration] = {}
        self.definitions: List[Definition] = []
        self.constraints: OrderedSet = OrderedSet()
        self.assignments: Assignments = Assignments()
        self.def_constraints: Dict[Tuple[SymbolDeclaration, Definition], List[Expression]] = {}
        self.interpretations: Dict[str, SymbolInterpretation] = {}  # interpretations given by user
        self.extensions: Dict[str, Extension] = {}  # computed extension of types and predicates
        self.name: str = ''

        self._uninterpreted_types = None  # list of types without interpretation
        self._contraintz: Optional[List[BoolRef]] = None  # list of constraints in Z3 form
        self._formula: Optional[BoolRef] = None  # the problem expressed in one logic formula
        self.co_constraints: Optional[OrderedSet] = None  # Constraints attached to subformula. (see also docs/zettlr/Glossary.md)

        self.z3: Dict[str, ExprRef] = {}
        self.ctx: Context = Context()
        self._constraintz = None
        self.add(*theories)

        self.previous_assignments: Assignments = Assignments()

        self.satisfied: bool = True

        self._slvr: Solver = None
        self._optmz: Solver = None
        self._reif: Solver = None
        self._optmz_reif: Solver = None

        self.expl_reifs: Dict[BoolRef: (BoolRef,Expression)] = {}  # {reified: (constraint, original)}
        self.ignored_laws: set[str] = set()


    @property
    def solver(self) -> Solver:
        "Beware that the setting of timeout_seconds (e.g. in expand()) is not thread safe"
        if self._slvr is None:
            self._slvr = Solver(ctx=self.ctx)
            if self.constraintz():
                self._slvr.add(And(self.constraintz()))
            assignment_forms = [a.formula().translate(self)
                                for a in self.assignments.values()
                                if a.value is not None
                                and (a.status == S.UNIVERSAL
                                     or (a.status == S.STRUCTURE
                                         and a.symbol_decl.needs_interpretation))]
            self._slvr.add(assignment_forms)
        return self._slvr

    @property
    def optimize_solver(self) -> Solver:
        if self._optmz is None:
            self._optmz = Optimize(ctx=self.ctx)
            if self.constraintz():
                self._optmz.add(And(self.constraintz()))
            assignment_forms = [a.formula().translate(self)
                                for a in self.assignments.values()
                                if a.value is not None
                                and (a.status == S.UNIVERSAL
                                     or (a.status == S.STRUCTURE
                                         and a.symbol_decl.needs_interpretation))]
            self._optmz.add(assignment_forms)
        return self._optmz

    @property
    def solver_reified(self) -> Solver:
        if self._reif is None:
            self._reif = Solver(ctx=self.ctx)
            # self._reif.set(':core.minimize', True)

            # get expanded def_constraints
            def_constraints = {}
            for defin in self.definitions:
                instantiables = defin.get_instantiables(self.interpretations, self.extensions, for_explain=True)
                defin.add_def_constraints(instantiables, self, def_constraints)

            for constraint in chain([c.interpret(self) for c in self.constraints],
                                    chain(*def_constraints.values())):
                p = constraint.reified(self)
                self.expl_reifs[p] = (constraint.translate(self), constraint)
                self._reif.add(Implies(p, self.expl_reifs[p][0]))

        return self._reif

    @property
    def optimize_solver_reified(self) -> Solver:
        if self._optmz_reif is None:
            _ = self.solver_reified  # ensure self.expl_reifs is instantiated
            self._optmz_reif = Optimize(ctx=self.ctx)
            for z3_reif, (z3_orig, _) in self.expl_reifs.items():
                self._optmz_reif.add(Implies(z3_reif, z3_orig))

        return self._optmz_reif

    def copy(self) -> "Theory":
        """Returns an independent copy of a theory.
        """
        out = copy(self)
        out.assignments = self.assignments.copy()
        out.constraints = OrderedSet(deepcopy(c) for c in self.constraints)
        out.declarations = {k:copy(v) for k,v in out.declarations.items()}
        out.interpretations = copy(out.interpretations)
        out.def_constraints = {k:[e for e in v]  #TODO e.copy()
                               for k,v in self.def_constraints.items()}
        # copy() is called before making substitutions => invalidate derived fields
        out._uninterpreted_types = [out.declarations[decl.name]
            for decl in self._uninterpreted_types
        ]
        out._formula = None
        return out

    def add(self, *theories: Union[TheoryBlock, Structure, "Theory"]) -> "Theory":
        """Adds a list of theories to the theory.

        Args:
            theories (Union[TheoryBlock, Structure, Theory]): 1 or more (data) theories.
        """
        for block in theories:
            self.z3 = {}
            self._formula = None  # need to reapply the definitions

            for name, decl in block.declarations.items():
                assert (name not in self.declarations
                        or self.declarations[name] == block.declarations[name]
                        or name in RESERVED_SYMBOLS), \
                        f"Can't add declaration for {name} in {block.name}: duplicate"
                self.declarations[name] = decl

            # reset the interpretations of TypeDeclaration
            for decl in self.declarations.values():
                if type(decl) == TypeDeclaration:
                    decl.interpretation = (  #TODO side-effects ? issue #81
                        None if decl.name not in [INT, REAL, DATE, CONCEPT] else
                        decl.interpretation)

            # process block.interpretations
            for name, interpret in block.interpretations.items():
                assert (name not in self.interpretations
                        or name in [INT, REAL, DATE, CONCEPT]
                        or self.interpretations[name] == block.interpretations[name]), \
                        f"Can't add enumeration for {name} in {block.name}: duplicate"
                self.interpretations[name] = interpret

            if isinstance(block, TheoryBlock) or isinstance(block, Theory):
                self.co_constraints = None
                self.definitions += block.definitions
                self.constraints.extend(deepcopy(v) for v in block.constraints)
                self.def_constraints.update(
                    {k:deepcopy(v) for k,v in block.def_constraints.items()})
        self._interpret()
        return self

    def _interpret(self) -> bool:
        """ Tries to interpret the theory.  Returns True if successful """

        self._uninterpreted_types = [decl
                    for decl in self.declarations.values()
                    if type(decl) == TypeDeclaration
                    and decl.name not in [BOOL, CONCEPT]
                    and self.interpretations.get(decl.name, None) is None]

        if self._uninterpreted_types:
            return False

        # apply the enumerations and definitions

        self.assignments = Assignments()
        self.extensions = {}  # reset the cache

        for decl in self.declarations.values():
            if type(decl) == SymbolDeclaration:  # reset it
                decl.needs_interpretation = False
            decl.interpret(self)

        # remove RELEVANT constraints
        self.constraints = OrderedSet([v for k,v in self.constraints.items()
            if not(type(v) == AppliedSymbol
                   and v.decl is not None
                   and v.decl.name == RELEVANT)])

        # expand goal_symbol
        symbol_interpretation = self.interpretations.get(GOAL_SYMBOL, None)
        if symbol_interpretation:
            for t in symbol_interpretation.enumeration.tuples:
                symbol = t.args[0]
                decl = self.declarations[symbol.name[1:]]
                assert decl.instances, f"goal {decl.name} must be instantiable."
                relevant = SYMBOL(RELEVANT)
                relevant.decl = self.declarations[RELEVANT]
                for i in decl.instances.values():
                    constraint = AppliedSymbol.make(relevant, [i])
                    self.constraints.append(constraint)

        # expand whole-domain definitions
        for defin in self.definitions:
            defin.interpret(self)

        # initialize assignments, co_constraints, questions

        self.co_constraints, questions = OrderedSet(), OrderedSet()
        for c in self.constraints:
            c.interpret(self)  # may add co_constraints
            c.co_constraints(self.co_constraints)
            # don't collect questions from type constraints
            if not c.is_type_constraint_for:
                c.collect(questions, all_=False)
        for es in self.def_constraints.values():
            for e in es:
                e.co_constraints(self.co_constraints)
        for c in self.co_constraints.values():
            c.interpret(self)

        for s in list(questions.values()):
            if s.code not in self.assignments:
                self.assignments.assert__(s, None, S.UNKNOWN)

        self._constraintz = None
        return True

    def to_smt_lib(self) -> str:
        """Returns an SMT-LIB version of the theory
        """
        return self.solver.sexpr()

    def assert_(self,
                code: str,
                value: Any,
                status: S = S.GIVEN
                ) -> "Theory":
        """asserts that an expression has a value (or not), e.g. ``theory.assert_("p()", True)``

        Args:
            code (str): the code of the expression, e.g., ``"p()"``
            value (Any): a Python value, e.g., ``True``
            status (Status, Optional): how the value was obtained.  Default: S.GIVEN
        """
        atom = self.assignments[code].sentence
        if value is None:
            self.assignments.assert__(atom, None, S.UNKNOWN)
        else:
            val = str_to_IDP(atom, str(value))
            self.assignments.assert__(atom, val, status)
        self._formula = None

    def enable_law(self, code: str) -> "Theory":
        """Enables a law, represented as a code string taken from the output of explain(...).

        The law should not result from a structure (e.g., from ``p:=true.``)
        or from a types (e.g., from ``T:={1..10}`` and ``c: () -> T``).

        Args:
            code (str): the code of the law to be enabled

        Raises:
            AssertionError: if code is unknown
        """
        _ = self.solver_reified
        assert any(e.code == code
                   for _, e in self.expl_reifs.values()), \
                f"Cannot enable an unknown law: {code}"
        self.ignored_laws.remove(code)

    def disable_law(self, code: str) -> "Theory":
        """Disables a law, represented as a code string taken from the output of explain(...).

        The law should not result from a structure (e.g., from ``p:=true.``)
        or from a types (e.g., from ``T:={1..10}`` and ``c: () -> T``).

        Args:
            code (str): the code of the law to be disabled

        Raises:
            AssertionError: if code is unknown
        """
        _ = self.solver_reified
        assert any(e.code == code
                   for _, e in self.expl_reifs.values()), \
                f"Cannot disable an unknown law: {code}"
        self.ignored_laws.add(code)

    def constraintz(self) -> List[BoolRef]:
        """list of constraints, co_constraints and definitions in Z3 form"""
        if self._constraintz is None:
            assert not self._uninterpreted_types, (\
                f"Missing interpretation for "
                f"{','.join(decl.name for decl in self._uninterpreted_types)}.  "
                f"Consider using Theory(T).generate().")

            def collect_constraints(e, constraints):
                """collect constraints in e, flattening conjunctions"""
                if e.sexpr() == 'true':
                    return
                if is_and(e):
                    for e1 in e.children():
                        collect_constraints(e1, constraints)
                else:
                    constraints.append(e)

            self._constraintz = []
            for e in chain(self.constraints, self.co_constraints):
                collect_constraints(e.translate(self), self._constraintz)
            self._constraintz += [s.translate(self)
                            for s in chain(*self.def_constraints.values())]

        return self._constraintz

    def formula(self) -> BoolRef:
        """ Returns a Z3 object representing the logic formula equivalent to the theory.

        This object can be converted to a string using ``str()``.
        """
        if self._formula is None:
            if self.constraintz():
                # use existing z3 constraints, but only add interpretations
                # for those symbols, not propagated in a previous step,
                # occurring in the (potentially simplified) z3 constraints
                all = ([a.formula().translate(self)
                        for a in self.assignments.values()
                        if (a.status != S.STRUCTURE or a.symbol_decl.needs_interpretation)
                        and a.value is not None
                        and a.status not in [S.CONSEQUENCE, S.ENV_CONSQ]]
                        + self.constraintz())
            else:
                all = [a.formula().translate(self) for a in self.assignments.values()
                       if a.status in [S.DEFAULT, S.GIVEN, S.EXPANDED]]
            self._formula = And(all) if all != [] else BoolVal(True, self.ctx)
        return self._formula

    def get_core_atoms(self, statuses: List[S]) -> List[Assignment]:
        return [a for a in self.assignments.values()
            if (self.extended or not a.sentence.is_reified())
            and a.status in statuses]

    def sexpr(self) -> str:
        s = Solver(ctx=self.ctx)
        s.add(self.formula())
        return s.sexpr()


    def _is_defined(self, model, q):
        # determine if the expression is defined
        defined = True
        if type(q) == AppliedSymbol:
            if any(type(T.decl) != TypeDeclaration for T in q.decl.sorts):
                in_domain = q.decl.has_in_domain(q.sub_exprs, self.interpretations, self.extensions)
                if in_domain.same_as(FALSE):
                    defined = False
                elif in_domain.same_as(TRUE):
                    defined = True
                else:
                    defined = model.eval(in_domain.translate(self))
                    if str(defined) == str(in_domain):
                        defined = True  #TODO dubious. Why not False ?
        return defined

    def _is_undefined(self, solver, q):
        # determine if the expression is certainly undefined
        result = False
        if type(q) == AppliedSymbol:
            if any(type(T.decl) != TypeDeclaration for T in q.decl.sorts):
                in_domain = q.decl.has_in_domain(q.sub_exprs, self.interpretations, self.extensions)
                if in_domain.same_as(FALSE):
                    result = True
                elif in_domain.same_as(TRUE):
                    result = False
                else:
                    solver.push()
                    solver.add(in_domain.translate(self))
                    res = solver.check()
                    solver.pop()
                    result = res == unsat
        return result

    def _from_model(self,
                    solver: Solver,
                    todo: List[Expression],
                    complete: bool) -> Assignments:
        """ returns Assignments from model in solver

        the solver must be in sat state
        """
        ass = copy(self.assignments)
        model = solver.model()
        for q in todo:
            assert self.extended or not q.is_reified(), \
                    "Reified atom should only appear in case of extended theories"

            a = ass[q.code]
            if not self._is_defined(model, q):
                a.value, a.tag, a.relevant = None, S.UNKNOWN, False
            else:
                if complete or q.is_reified():
                    val1 = model.eval(q.reified(self), model_completion=complete)
                else:
                    val1 = model.eval(q.translate(self), model_completion=complete)
                val = str_to_IDP(q, str(val1))
                if val is not None:
                    if q.is_assignment() and val == FALSE:  # consequence of the TRUE assignment
                        tag = (S.ENV_CONSQ if q.sub_exprs[0].decl.block.name == 'environment'
                            else S.CONSEQUENCE)
                    else:
                        tag = S.EXPANDED
                    ass.assert__(q, val, tag)
                else:
                    a.value, a.tag, a.relevant = None, S.UNKNOWN, False
        return ass

    def _add_assignment(self, solver: Solver) -> None:
        """adds the current choices to the (non-reified) solver

        Args:
            solver (Z3 solver): the solver to add the assignments to
        """
        assignment_forms = [a.formula().translate(self) for a in
                            self.assignments.values()
                            if a.value is not None
                            and a.status in [S.GIVEN, S.EXPANDED, S.DEFAULT]]
        for af in assignment_forms:
            solver.add(af)

    def _extend_reifications(self,
                             reifs: Dict[ExprRef, Tuple[Assignment, Expression]]
                             ) -> None:
        """extends the given reifications with the current choices and structure

        Args:
            reifs (Dict[z3.BoolRef: (z3.BoolRef,Expression)]): reifications to
            be extended
        """
        for a in self.assignments.values():
            if a.status in [S.GIVEN, S.DEFAULT, S.STRUCTURE, S.EXPANDED]:
                p = a.translate(self)
                if a.status == S.STRUCTURE:
                    form = a.formula()
                    form.annotations['reading'] = ("Structure formula " +
                                                   form.annotations['reading'])
                else:
                    form = None
                reifs[p] = (a, form)

    def _add_assignment_ignored(self, solver: Solver) -> None:
        """adds the current choices to the reified solver
        and resets propagated assignments

        Args:
            solver (Z3 solver): the reified solver to add the assignments to
        """
        ps = self.expl_reifs.copy()
        self._extend_reifications(ps)
        for a in self.assignments.values():
            if a.status in [S.CONSEQUENCE, S.ENV_CONSQ, S.UNIVERSAL]:
                self.assignments.assert__(a.sentence, None, S.UNKNOWN)
        for z3_form, (_, expr) in ps.items():
            if not (expr and expr.code in self.ignored_laws):
                solver.add(z3_form)

    def expand(self,
               max: int = 10,
               timeout_seconds: int = 10,
               complete: bool = False
               ) -> Iterator[Union[Assignments, str]]:
        """Generates a list of models of the theory that are expansion of the known assignments.

        The result is limited to ``max`` models (10 by default), or unlimited if ``max`` is 0.
        The search for new models is stopped when processing exceeds ``timeout_seconds`` (in seconds) (unless it is 0).
        The models can be asked to be complete or partial (i.e., in which "don't care" terms are not specified).

        The string message can be one of the following:

        - ``No models.``

        - ``No model found in xx seconds.  Models may be available.  Change the timeout_seconds argument to see them.``

        - ``More models may be available.  Change the max argument to see them.``

        - ``More models may be available.  Change the timeout_seconds argument to see them.``

        - ``More models may be available.  Change the max and timeout_seconds arguments to see them.``

        Args:
            max (int, optional): maximum number of models. Defaults to 10.
            timeout_seconds (int, optional): timeout_seconds seconds.  Defaults to 10.
            complete (bool, optional): ``True`` for complete models. Defaults to False.

        Yields:
            the models, followed by a string message
        """
        start = time.time()
        if self.ignored_laws:
            # TODO: should todo be larger in case complete==True?
            solver = self.solver_reified
            solver.push()
            self._add_assignment_ignored(solver)
            if not self.previous_assignments:
                try:
                    list(self._first_propagate(solver))
                except IDPZ3Error:  # unsatifiable
                    yield "No models."
                    return
        else:
            # TODO: should todo be larger in case complete==True?
            solver = self.solver
            solver.push()
            self._add_assignment(solver)
        default_timeout = get_param("timeout")

        todo = OrderedSet(a.sentence for a in self.get_core_atoms([S.UNKNOWN]))

        for q in todo:
            if (q.is_reified() and self.extended) or complete:
                solver.add(q.reified(self) == q.translate(self))

        count, ass = 0, {}
        while ((max <= 0 or count < max) and
               (timeout_seconds <= 0 or time.time() - start < timeout_seconds)):
            if timeout_seconds:
                remaining = timeout_seconds - (time.time() - start)
                solver.set("timeout", int(remaining*1000+200))
            # exclude ass
            different = []
            for a in ass.values():
                if a.status == S.EXPANDED:
                    q = a.sentence
                    different.append(q.translate(self) != a.value.translate(self))
            if 0 < count and len(different) == 0:
                break
            if different:
                solver.add(Or(different))

            if solver.check() == sat:
                count += 1
                ass = self._from_model(solver, todo, complete)
                yield ass
            else:
                break

        solver.pop()

        maxed = (0 < max <= count)
        timeouted = (0 < timeout_seconds <= time.time()-start)
        # if interrupted by the timeout_seconds
        if maxed or timeouted:
            param = ("max and timeout_seconds arguments" if maxed and timeouted else
                     "max argument" if maxed else
                     "timeout_seconds argument")
            if count == 0:
                yield f"{NEWL}No model found in {timeout_seconds} seconds.  Models may be available.  Change the {param} to see them."
            else:
                yield f"{NEWL}More models may be available.  Change the {param} to see them."
        elif 0 < count:
            yield f"{NEWL}No more models."
        else:
            yield "No models."
        solver.set("timeout", int(default_timeout))

    def optimize(self,
                 term: str,
                 minimize: bool = True
                 ) -> "Theory":
        """Updates the value of `term` in the ``assignments`` property of `self`
        to the optimal value that is compatible with the theory.

        Chain it with a call to `expand` to obtain a model,
        or to `propagate` to propagate the optimal value.

        Args:
            term (str): e.g., ``"Length(1)"``
            minimize (bool): ``True`` to minimize ``term``, ``False`` to maximize it
        """
        assert term in self.assignments, "Internal error"
        sentence = self.assignments[term].sentence
        s = sentence.translate(self)

        if self.ignored_laws:
            solver = self.optimize_solver_reified
            solver.push()
            self._add_assignment_ignored(solver)
        else:
            solver = self.optimize_solver
            solver.push()
            self._add_assignment(solver)

        if minimize:
            solver.minimize(s)
        else:
            solver.maximize(s)
        res = solver.check()
        assert res == sat, "Optimization requires satisfiable specification"

        # deal with strict inequalities, e.g. min(0<x)
        val = solver.model().eval(s)
        for i in range(0, 10):
            if minimize:
                solver.add(s < val)
            else:
                solver.add(val < s)
            if solver.check() == sat:
                val = solver.model().eval(s)
            else:
                break
        solver.pop()

        val_IDP = str_to_IDP(sentence, str(val))
        if val_IDP is not None:
            self.assert_(str(sentence), val_IDP, S.GIVEN)
            ass = str(EQUALS([sentence, val_IDP]))
            if ass in self.assignments:
                self.assert_(ass, True, S.GIVEN)

        return self

    def symbolic_propagate(self, tag: S = S.UNIVERSAL) -> "Theory":
        """Returns the theory with its ``assignments`` property updated
        with direct consequences of the constraints of the theory.

        This propagation is less complete than ``propagate()``.

        Args:
            tag (S): the status of propagated assignments
        """
        for c in self.constraints:
            # determine consequences, including from co-constraints
            new_constraint = c.substitute(TRUE, TRUE, self.assignments, tag)
            new_constraint.symbolic_propagate(self.assignments, tag)
        return self

    def propagate(self,
                  tag: S = S.CONSEQUENCE,
                  method: Propagation = Propagation.DEFAULT
                  ) -> "Theory":
        """Returns the theory with its ``assignments`` property updated
        with values for all terms and atoms that have the same value
        in every model of the theory.

       ``self.satisfied`` is also updated to reflect satisfiability.

        Terms and propositions starting with ``_`` are ignored.

        Args:
            tag (S): the status of propagated assignments
            method (Propagation): the particular propagation to use
        """
        if method == Propagation.BATCH:
            # NOTE: running this will confuse _directional_todo, not used right now
            assert False, "dead code"
            out = list(self._batch_propagate(tag))
        if method == Propagation.Z3:
            # NOTE: running this will confuse _directional_todo, not used right now
            assert False, "dead code"
            out = list(self._z3_propagate(tag))
        else:
            out = list(self._propagate(tag=tag))
        self.satisfied = (out[0] != NOT_SATISFIABLE)
        return self

    def get_range(self, term: str) -> List[str]:
        """Returns a list of the possible values of the term.

        Args:
            term (str): terms whose possible values are requested, e.g. ``subtype()``.
                Must be a key in ``self.assignments``

        Returns:
            List[str]: e.g., ``['right triangle', 'regular triangle']``
        """
        assert term in self.assignments, f"Unknown term: {term}"
        termE : Expression = self.assignments[term].sentence
        assert type(termE) == AppliedSymbol, f"{term} is not a term"
        range = termE.decl.range
        assert range, f"Can't determine range on infinite domains"

        # consider every value in range
        atoms = [Assignment(termE, val, S.UNKNOWN).formula() for val in range]
        todos = {a.code: a for a in atoms}

        # initialize the forbidden values
        forbidden = set(str(e.sub_exprs[1]) for e in todos.values()
                        if str(e) in self.assignments
                        and self.assignments[str(e)].status in [S.GIVEN]
                        and self.assignments[str(e)].value.same_as(FALSE))

        #  remove current assignments to same term
        backup = self.assignments
        self.assignments = self.assignments.copy()
        removed = []
        if self.assignments[term].value:
            for k,a in self.assignments.items():
                if (a.sentence.is_assignment and
                        a.sentence.code.startswith(term) and
                        a.status in [S.GIVEN, S.DEFAULT, S.EXPANDED]):
                    self.assert_(k, None, S.UNKNOWN)
                    removed.append(a)

        for ass in self._propagate(given_todo=todos):
            if isinstance(ass, str):
                continue
            if ass.value.same_as(FALSE):
                forbidden.add(str(ass.sentence.sub_exprs[1]))

        # restore the assignments
        self.assignments = backup

        return [str(e.sub_exprs[1]) for e in todos.values()
                if str(e.sub_exprs[1]) not in forbidden]

    def explain(self,
                consequence: Optional[str] = None,
                timeout_seconds: int = 0
                ) -> Tuple[List[Assignment], List[Expression]]:
        """Returns the facts and laws that make the Theory unsatisfiable, or that explains a consequence.
        Raises an IDPZ3Error if the Theory is satisfiable

        Args:
            self (Theory): the problem state
            consequence (string, optional): the code of the consequence to be explained.  Must be a key in ``self.assignments``

        Returns:
            (List[Assignment], List[Expression])]: list of facts and laws that explain the consequence
        """

        start = time.time()
        solver = self.solver_reified
        default_timeout = get_param("timeout")
        ps = self.expl_reifs.copy()
        self._extend_reifications(ps)

        solver.push()

        if consequence:
            negated = consequence.replace('~', '¬').startswith('¬')
            consequence = consequence[1:] if negated else consequence
            assert consequence in self.assignments, \
                f"Can't find this sentence: {consequence}"

            to_explain = self.assignments[consequence].sentence

            # rules used in justification
            if to_explain.type != BOOL:  # determine numeric value
                val = self.assignments[consequence].value
                if val is None:  # can't explain an expanded value
                    solver.pop()
                    return [], []
                to_explain = EQUALS([to_explain, val])
            if negated:
                to_explain = NOT(to_explain)

            solver.add(Not(to_explain.translate(self)))

        if timeout_seconds:
            solver.set("timeout", int(timeout_seconds*1000))
        result = solver.check([z3_form for z3_form, (_, expr) in ps.items() if
                                    not (expr and expr.code in self.ignored_laws)])

        solver.set("timeout", int(default_timeout))
        if not timeout_seconds or time.time() - start < timeout_seconds:
            if result == sat:
                raise IDPZ3Error("Theory is satisfiable: nothing to explain.")
            unsatcore = solver.unsat_core()  # does not respect timeout ?!

            solver.pop()

            facts, laws = [], []
            if unsatcore:
                facts = [ps[a][0] for a in unsatcore if ps[a][1] is None]
                laws = [ps[a][1] for a in unsatcore if ps[a][1] is not None]

            return facts, laws
        else:
            return [], []

    def simplify(self) -> "Theory":
        """ Returns a simpler copy of the theory, with a simplified formula
        obtained by substituting terms and atoms by their known values.

        Assignments obtained by propagation become UNIVERSAL constraints.
        """
        out = self.copy()

        # convert consequences to Universal
        for ass in out.assignments.values():
            if ass.value:
                # TODO: what if consequences are due to choices (e.g., defaults?)
                ass.status = (S.UNIVERSAL if ass.status in [S.CONSEQUENCE, S.ENV_CONSQ] else
                        ass.status)

        new_constraints: List[Expression] = []
        for constraint in out.constraints:
            new_constraint = constraint.simplify_with(out.assignments)
            new_constraints.append(new_constraint)
        out.constraints = new_constraints
        out._formula, out._constraintz = None, None
        return out

    def determine_relevance(self) -> "Theory":
        # monkey-patched
        pass

    def _generalize(self,
                    conjuncts: List[Assignment],
                    known: BoolRef,
                    z3_formula: Optional[BoolRef] = None
                    ) -> List[Assignment]:
        """finds a subset of `conjuncts`
            that is still a minimum satisfying assignment for `self`, given `known`.

        Args:
            conjuncts (List[Assignment]): a list of assignments
                The last element of conjuncts is the goal or TRUE
            known: a z3 formula describing what is known (e.g. reification axioms)
            z3_formula: the z3 formula of the problem.
                Can be supplied for better performance

        Returns:
            [List[Assignment]]: A subset of `conjuncts`
                that is a minimum satisfying assignment for `self`, given `known`
        """
        if z3_formula is None:
            z3_formula = self.formula()

        conditions, goal = conjuncts[:-1], conjuncts[-1]
        # verify satisfiability
        solver = Solver(ctx=self.ctx)
        z3_conditions = (TRUE.translate(self) if len(conditions)==0 else
                         And([l.translate(self) for l in conditions]))
        solver.add(And(z3_formula, known, z3_conditions))
        if solver.check() != sat:
            return []
        else:
            for i, c in (list(enumerate(conditions))): # optional: reverse the list
                if 1< len(conditions):
                    conditions_i = And([l.translate(self)
                                        for j, l in enumerate(conditions)
                                        if j != i])
                else:
                    conditions_i = TRUE.translate(self)
                solver = Solver(ctx=self.ctx)
                if goal.sentence == TRUE or goal.value is None:  # find an abstract model
                    # z3_formula & known & conditions => conditions_i is always true
                    solver.add(Not(Implies(And(known, conditions_i), z3_conditions)))
                else:  # decision table
                    # z3_formula & known & conditions => goal is always true
                    hypothesis = And(z3_formula, known, conditions_i)
                    solver.add(Not(Implies(hypothesis, goal.translate(self))))
                if solver.check() == unsat:
                    conditions[i] = Assignment(TRUE, TRUE, S.UNKNOWN)
            conditions = join_set_conditions(conditions)
            return [c for c in conditions if c.sentence != TRUE]+[goal]

    def decision_table(self,
                       goal_string: str = "",
                       timeout_seconds: int = 20,
                       max_rows: int = 50,
                       first_hit: bool = True,
                       verify: bool = False
                       ) -> Tuple[List[List[Assignment]], bool]:
        """Experimental.  Returns the rows for a decision table that defines ``goal_string``.

        ``goal_string`` must be a predicate application defined in the theory.
        The theory must be created with ``extended=True``.

        Args:
            goal_string (str, optional): the last column of the table.
            timeout_seconds (int, optional): maximum duration in seconds. Defaults to 20.
            max_rows (int, optional): maximum number of rows. Defaults to 50.
            first_hit (bool, optional): requested hit-policy. Defaults to True.
            verify (bool, optional): request verification of table completeness.  Defaults to False

        Returns:
            list(list(Assignment)): the non-empty cells of the decision table  for ``goal_string``, given ``self``.
            bool: whether or not the timeout limit was reached.
        """
        timeout_hit = False
        max_time = time.time()+timeout_seconds  # 20 seconds max
        assert self.extended == True, \
            "The problem must be created with 'extended=True' for decision_table."

        # determine questions, using goal_string and self.constraints
        questions = OrderedSet()
        if goal_string:
            goal_pred = goal_string.split("(")[0]
            assert goal_pred in self.declarations, (
                f"Unrecognized goal string: {goal_string}")
            for (decl, _),es in self.def_constraints.items():
                if decl != self.declarations[goal_pred]: continue
                for e in es:
                    e.collect(questions, all_=True)
            for q in questions:  # update assignments for defined goals
                if q.code not in self.assignments:
                    self.assignments.assert__(q, None, S.UNKNOWN)
        for c in self.constraints:
            if not c.is_type_constraint_for:
                c.collect(questions, all_=False)
        # ignore questions about defined symbols (except goal)
        symbols = {decl for defin in self.definitions
                   for decl in defin.canonicals.keys()}
        qs = OrderedSet()
        for q in questions.values():
            if (goal_string == q.code
            or any(s not in symbols
                   for s in q.collect_symbols(co_constraints=False).values())):
                qs.append(q)
        questions = qs
        assert not goal_string or goal_string in [a.code for a in questions], \
            f"Internal error"

        known = ([ass.translate(self) for ass in self.assignments.values()
                        if ass.status != S.UNKNOWN]
                    + [q.reified(self)==q.translate(self) for q in questions
                        if q.is_reified()])
        known = (And(known) if known else TRUE.translate(self))

        self._formula = None
        theory = self.formula()
        solver = Solver(ctx=self.ctx)
        solver.add(theory)
        solver.add(known)

        models, count = [], 0
        while (solver.check() == sat  # for each parametric model
               and count < max_rows and time.time() < max_time):
            # find the interpretation of all atoms in the model
            assignments = []  # [Assignment]
            model = solver.model()
            goal = None
            for atom in questions.values():
                assignment = self.assignments.get(atom.code, None)
                if assignment and assignment.value is None and atom.type == BOOL:
                    if not atom.is_reified():
                        val1 = model.eval(atom.translate(self))
                    else:
                        val1 = model.eval(atom.reified(self))
                    if val1 == True:
                        ass = Assignment(atom, TRUE, S.UNKNOWN)
                    elif val1 == False:
                        ass = Assignment(atom, FALSE, S.UNKNOWN)
                    else:
                        ass = Assignment(atom, None, S.UNKNOWN)
                    if atom.code == goal_string:
                        goal = ass
                    elif ass.value is not None:
                        assignments.append(ass)
            if verify:
                assert not goal_string or goal.value is not None, \
                    "The goal is not always determined by the theory"
            # start with negations !
            assignments.sort(key=lambda l: (l.value==TRUE, str(l.sentence)))
            assignments.append(goal if goal_string else
                                Assignment(TRUE, TRUE, S.UNKNOWN))

            assignments = self._generalize(assignments, known, theory)
            models.append(assignments)

            # add constraint to eliminate this model
            modelZ3 = Not(And( [l.translate(self) for l in assignments
                if l.value is not None] ))
            solver.add(modelZ3)

            count +=1
        if time.time() > max_time:
            timeout_hit = True

        if verify:
            def verify_models(known, models, goal_string):
                """verify that the models cover the universe

                Args:
                    known ([type]): [description]
                    models ([type]): [description]
                    goal_string ([type]): [description]
                """
                known2 = known
                for model in models:
                    condition = [l.translate(self) for l in model
                                    if l.value is not None
                                    and l.sentence.code != goal_string]
                    known2 = (And(known2, Not(And(condition))) if condition else
                              FALSE.translate(self))
                solver = Solver(ctx=self.ctx)
                solver.add(known2)
                assert solver.check() == unsat, \
                    "The DMN table does not cover the full domain"
            verify_models(known, models, goal_string)

        models.sort(key=len)

        if first_hit:
            known2 = known
            models1, last_model = [], []
            while models and time.time() < max_time:
                if len(models) == 1:
                    models1.append(models[0])
                    break
                model = models.pop(0).copy()
                condition = [l.translate(self) for l in model
                                if l.value is not None
                                and l.sentence.code != goal_string]
                if condition:
                    possible = Not(And(condition))
                    if verify:
                        solver = Solver(ctx=self.ctx)
                        solver.add(known2)
                        solver.add(possible)
                        result = solver.check()
                        assert result == sat, \
                            "A row has become impossible to trigger"
                    known2 = And(known2, possible)
                    models1.append(model)
                    models = [self._generalize(m, known2, theory)
                        for m in models]
                    models = [m for m in models if m] # ignore impossible models
                    models = list(dict([(",".join([str(c) for c in m]), m)
                                        for m in models]).values())
                    models.sort(key=len)
                else: # when not deterministic
                    last_model += [model]
            models = models1 + last_model
            # post process if last model is just the goal
            # replace [p=>~G, G] by [~p=>G]
            if (len(models[-1]) == 1
            and models[-1][0].sentence.code == goal_string
            and models[-1][0].value is not None):
                last_model = models.pop()
                hypothesis, consequent = [], last_model[0].negate()
                while models:
                    last = models.pop()
                    if (len(last) == 2
                    and last[-1].sentence.code == goal_string
                    and last[-1].value.same_as(consequent.value)):
                        hypothesis.append(last[0].negate())
                    else:
                        models.append(last)
                        break
                hypothesis.sort(key=lambda l: (l.value==TRUE, str(l.sentence)))
                model = hypothesis + [last_model[0]]
                model = self._generalize(model, known, theory)
                models.append(model)
                if hypothesis:
                    models.append([consequent])

            # post process to merge similar successive models
            # {x in c1 => g. x in c2 => g.} becomes {x in c1 U c2 => g.}
            # must be done after first-hit transformation
            for i in range(len(models)-1, 0, -1):  # reverse order
                m, prev = models[i], models[i-1]
                if (len(m) == 2 and len(prev) == 2
                    and m[1].same_as(prev[1])):  # same goals
                    # p | (~p & q) = ~(~p & ~q)
                    new = join_set_conditions([prev[0].negate(), m[0].negate()])
                    if len(new) == 1:
                        new = new[0].negate()
                        models[i-1] = [new, models[i-1][1]]
                        del models[i]
            if time.time() > max_time:
                timeout_hit = True
            if verify:
                verify_models(known, models, goal_string)

        return (models, timeout_hit)

    def _first_propagate(self, solver):
        """monkey-patched"""
        print()
        pass

    def generate(self,
                 guess: Dict[str, int] = None,
                 factor: float = 0,
                 timeout_seconds: int = 10,
                 unsat_seconds: int = 5
                 ) -> Tuple[str, Assignments]:
        """Solve generative configuration problems, using an iterative method

        The types without interpretations are initially assumed to have 1 object
        (or a size given by dictionary `guess`)
        and, if the theory is unsatisfiable, are grown until a model is found.
        The growth is by 1, or by the multiplying `factor` (if higher than 1).

        Returns:
            str: a string describing a structure
            that interprets the uninterpreted types of self

            Assignments: a model expansion of self
            using the found interpretation of the uninterpreted types
        """
        start = time.time()
        #TODO check that new identifiers won't conflict with existing symbols
        assert 0 <= factor, f"factor must be positive: {factor}"

        # create guess, if necessary
        guess = {} if guess is None else guess
        for decl in self._uninterpreted_types:
            if decl.name not in guess:
                guess[decl.name] = 0
            else:
                assert 0 < guess[decl.name]

        found = False
        max_time = start + timeout_seconds
        while not found and (time.time() < max_time or timeout_seconds <= 0):
            logging.info(f"Generate with n={guess}")
            th = self.copy()
            th.z3={}
            interpretations = ""
            for decl in self._uninterpreted_types:

                # create the enumeration
                if len(self._uninterpreted_types) == 1:  # monotype -> range
                    enumeration = Ranges(
                        elements = [RangeElement(fromI=Number(number='1'),
                                                toI=Number(number=str(guess[decl.name])))])
                else:  # typed -> evocative names
                    tuples = []
                    for j in range(guess[decl.name]):
                        name = f"{decl.name[0]}{j+1}"
                        assert (name not in decl.voc.symbol_decls
                                or type(decl.voc.symbol_decls[name]) == Constructor), \
                            f"Duplicate name {name}"
                        decl.voc.symbol_decls.pop(name, None)
                        tuples.append(TupleIDP(args=[UnappliedSymbol(None, s=SYMBOL(name=name))]))
                    enumeration=Enumeration(tuples=tuples)

                # create the interpretation
                interp = SymbolInterpretation(name=SYMBOL(name=decl.name), sign=':=',
                                enumeration=enumeration, default=None)
                decl.interpretation = interp
                th.interpretations[decl.name] = interp
                interpretations += f"{interp}. "

                # annotate the interpretation
                decl.constructors = []
                del decl.voc.symbol_decls[decl.name]
                decl.annotate(decl.voc)

            assert th._interpret(), 'Internal error'

            def collect_types(expr: Expression, types) -> List[str]:
                if type(expr) in [AQuantification, AAggregate] and expr.quantees:
                    for q in expr.quantees:
                        types.add(q.sub_exprs[0].decl.base_type.name)
                    collect_types(expr.f, types)
                elif (type(expr) == UnappliedSymbol
                      and type(expr.decl) == Constructor
                      and expr.decl.type not in [BOOL, CONCEPT]):
                    types.add(expr.decl.type)
                elif (type(expr) == AppliedSymbol):
                    if expr.symbol.decl.out.decl.base_type is not None:
                        types.add(expr.symbol.decl.out.decl.base_type.name)
                    for e in expr.sub_exprs:
                        collect_types(e, types)
                else:
                    for e in expr.sub_exprs:
                        collect_types(e, types)

            remaining = (0 if not timeout_seconds else
                         timeout_seconds - (time.time() - start))

            if len(self._uninterpreted_types) == 1:  # monotype
                model = next(th.expand(max=1, timeout_seconds=unsat_seconds))
                if type(model) == str:
                    for decl in self._uninterpreted_types:
                        prev_i = guess[decl.name]
                        i = prev_i+1 if factor == 0 else int(prev_i * factor)
                        guess[decl.name] = i+1 if i == prev_i else i
                else:
                    found = True
            else:  # typed --> compute unsat core
                try:
                    _, laws = th.explain(timeout_seconds = unsat_seconds)
                except IDPZ3Error as e1:  # satisfiable -> compute the model
                    found, laws = True, []

                if found:
                    model = next(th.expand(max=1, timeout_seconds=remaining))
                else:
                    if not laws:  # timeout
                        model = "No models found."
                    types = set()
                    for e in laws:
                        #logging.info(str(e.original))
                        collect_types(e.original, types)
                        if e.is_type_constraint_for is not None:  # for empty types
                            out = self.declarations[e.is_type_constraint_for].type
                            types.add(self.declarations[out].base_type.name)
                    for decl in (types if types else
                                 (t.name for t in self._uninterpreted_types)):
                        if decl in guess:
                            prev_i = guess[decl]
                            i = prev_i+1 if factor == 0 else int(prev_i * factor)
                            guess[decl] = i+1 if i == prev_i else i
        return interpretations, model

    def transform(self,
                  monotype: bool = False,
                  factor: float = 0,
                  lift: bool = True
                  ) -> Tuple[str, Theory]:
        """ returns a transformed theory of self, and its source code

        If `monotype` is True, a generic `ConfigObject` type is created,
        combining the uninterpreted types.
        If `factor` is not 0, the tranformed vocabulary supports unused `ConfigObject`.
        If `lift` is True, the theory is lifted.
        """
        source = transform(self, monotype, factor, lift)
        return source, Theory(IDP.from_str(source).theories['T'])

    def expand_lifting(self,
                      lifted_model: Assignments
                      ) -> str:
        """ returns a string describing a concrete model
        """
        out = []
        # compute expansions of lifted objects
        types = {f"{decl.name}": [] for decl in self._uninterpreted_types}
        expansions = {}
        count = 1
        for a in lifted_model.values():  # for each mul*() symbols
            if (type(a.sentence) == AppliedSymbol
            and len(a.sentence.sub_exprs) == 1
            and a.sentence.code.startswith("mul")  #TODO better recognize mul
            and a.value is not None):
                # if a.value is not None: print(a.sentence.code)
                lo = a.sentence.sub_exprs[0]
                prefix = a.sentence.code[3]+lo.str if type(lo) == Number else lo
                exp = [f"{count+i}" for i in range(a.value.py_value)]  # use integers in case of ConfigObj
                count += a.value.py_value
                expansions[lo.str] = exp
                types[a.sentence.symbol.code[3:]].extend(exp)

        # interpretation of types
        for decl in self._uninterpreted_types:
            out.append(f"{decl.name} := {{{', '.join(types[decl.name])}}}.")

        def expand(term: Expression) -> List[str]:
            "returns the expansion of a lifted object, or the term itself"
            return expansions.get(term.str, [term.str])

        # interpretation of symbols
        symbols = {}
        for a in lifted_model.values():
            if (type(a.sentence) == AppliedSymbol
            and a.symbol_decl.name in self.declarations
            and not a.sentence.code.startswith("mul")  #TODO better recognize mul
            and not a.sentence.code.startswith("max")  #TODO better recognize max
            and a.value is not None
            and not a.sentence.symbol.name in self.interpretations):
                lifted_args = a.sentence.sub_exprs
                lifted_val = a.value
                argss, vals = [expand(e) for e in lifted_args], expand(lifted_val)
                mul = math.prod(len(e) for e in argss)

                c = []
                if len(lifted_args) == 0:  # constant value
                    c.append(f"-> {lifted_val}")
                elif mul != 0:  # ignore unused objects
                    vals = (mul//len(vals)) * vals
                    argss = [(mul//len(e)) * e for e in argss]

                    for val, *args in zip(vals, *argss):
                        tuple = ", ".join(str(e) for e in args)
                        tuple = f"({tuple})" if 1 < len(a.sentence.sub_exprs) else tuple

                        if val == 'false':
                            # make sure we have an entry for `a` in `out`
                            if a.symbol_decl.name not in symbols:
                                symbols[a.symbol_decl.name] = []
                        elif val == 'true':
                            # Symbol is a predicate.
                            c.append(f"{tuple}")
                        elif val != 'None':
                            # Symbol is a function.
                            c.append(f"{tuple} -> {val}")

                if c:
                    enum = symbols.get(a.symbol_decl.name, [])
                    enum.extend(c)
                    symbols[a.symbol_decl.name] = enum

        for k, enum in symbols.items():
            out.append(f"{k} := {{{', '.join(enum)}}}.")

        return "\n".join(out)


Done = True
