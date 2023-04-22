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

Method to transform a Theory into its lifted form:

* Theory.transform(monotype, factor, lift)

`todo` is a dictionary {(Ts_string, (None|decl.name|term.str)) : (xs, None|y, None|term)}

TODO:
* min, max aggregates
* inductive search of guards
* division
* Simplify additional sentences using strings
* Avoid q_vars by annotating variables with their quantee

"""
from __future__ import annotations

from copy import deepcopy, copy
import re
from typing import Dict, List, Optional, TYPE_CHECKING
if TYPE_CHECKING:
    from .Theory import Theory

from .Parse import Vocabulary, TypeDeclaration, SymbolDeclaration
from .Expression import (Expression, IF, AIfExpr, AComparison, Quantee, SymbolExpr, AQuantification, AAggregate,
                         AppliedSymbol, UnappliedSymbol, AUnary, EQUALS, FORALL, EXISTS, TYPE,
                         AImplication, AConjunction, ADisjunction, AEquivalence, ASumMinus, AMultDiv,
                         SYMBOL, Number, Variable, VARIABLE, TRUE, FALSE, ZERO, ONE, Brackets)
from .utils import INT, BOOL, NEWL, OrderedSet


def transform(self,
                monotype: bool = False,
                factor: float = 0,
                lift: bool = True
                ) -> str:
    """ returns the source code of a transformed theory of self

    If `monotype` is True, a generic `ConfigObject` type is created,
    combining the uninterpreted types.
    If `factor` is not 0, the tranformed vocabulary supports unused `ConfigObject`.
    If `lift` is True, the theory is lifted.
    """
    assert 0 < len(self._uninterpreted_types), \
        "Can't transform theory without uninterpreted types"
    th = self.copy()

    # swap copy of symbol_decls (because voc is unfortunately shared)
    voc = th._uninterpreted_types[0].voc
    new_symbol_decls = {k:copy(v) for k,v in voc.symbol_decls.items()}
    voc.symbol_decls, new_symbol_decls = new_symbol_decls, voc.symbol_decls

    new_symbols, new_definition = {}, ""

    # remove interpretation of uninterpreted types
    for decl in th._uninterpreted_types:
        decl.constructors = None

    new_constraints = []

    if monotype:
        pre_declarations = {}

        # type ConfigObj
        config = TypeDeclaration(name='ConfigObject')
        config.lift = True
        config.annotate(voc)
        pre_declarations['ConfigObject'] = config

        for decl in th._uninterpreted_types:
            # type A --> A: ConfigObject -> Bool
            del th.declarations[decl.name]
            symb = SYMBOL(name=decl.name)
            decl = SymbolDeclaration(annotations='', name=symb,
                                        sorts=[TYPE(name='ConfigObject')],
                                        out=TYPE(name=BOOL))
            decl.lift = True
            decl.annotate(voc)
            pre_declarations[decl.name] = decl

            # max_T: () -> Int
            max = SYMBOL(name=f"max{decl.name}")
            symb_decl = SymbolDeclaration(annotations='', name=max,
                                        sorts=[], out=TYPE(name=INT))
            symb_decl.lift = True
            symb_decl.block = voc
            symb_decl.annotate(voc)
            max.decl = symb_decl
            th.declarations[max.name] = symb_decl

        if factor != 0:
            # UNUSED : ConfigObj -> Bool
            symb = SYMBOL(name='UNUSED')
            decl = SymbolDeclaration(annotations='', name=symb,
                                        sorts=[TYPE(name='ConfigObject')],
                                        out=TYPE(name=BOOL))
            decl.lift = True
            decl.annotate(voc)
            pre_declarations[decl.name] = decl
            th._uninterpreted_types.append(decl)

            # max_UNUSED: () -> Int
            max = SYMBOL(name=f"maxUNUSED")
            symb_decl = SymbolDeclaration(annotations='', name=max,
                                        sorts=[], out=TYPE(name=INT))
            symb_decl.lift = True
            symb_decl.block = voc
            symb_decl.annotate(voc)
            max.decl = symb_decl
            th.declarations[max.name] = symb_decl

        th.declarations = {**pre_declarations, **th.declarations}

        # type TypeConfigObject := {A, B, UNUSED}
        types = ', '.join(decl.name+"__" for decl in th._uninterpreted_types)
        new_symbols['TypeConfigObject'] = f"type TypeConfigObject := {{{types}}}"

        # typeConfigObject : ConfigObject -> TypeConfigObject
        new_symbols['typeConfigObject'] = "typeConfigObject : ConfigObject -> TypeConfigObject"

        # definition of typeConfigObject
        definition = "\n      ".join(f"!x in ConfigObject: typeConfigObject(x)={decl.name}__ <- {decl.name}(x)"
                                        + (f"& 0 < mulConfigObject(x)." if lift else ".")
                                for decl in th._uninterpreted_types)
        new_definition = f"{{ {definition}{NEWL}    }}{NEWL}"

        # symmetry breaking rules
        rules, prev = "", "1"
        for decl in th._uninterpreted_types:
            rules += f"      !x in ConfigObject: typeConfigObject(x)={decl.name}__ <- {prev} =< x < max{decl.name}().\n"
            prev = f"max{decl.name}()"
        new_definition += f"    {{{NEWL}{rules}    }}{NEWL}"

        th._uninterpreted_types = [config]

    elif not monotype:  # add predicate for unused
        pre_declarations = {}

        for decl in th._uninterpreted_types:
            # type A_T
            A_Tname = f"{decl.name}_T"
            A_T = TypeDeclaration(name=A_Tname)
            A_T.lift = True
            A_T.annotate(voc)
            pre_declarations[A_Tname] = A_T

            # A: A_T -> Bool
            del th.declarations[decl.name]
            symb = SYMBOL(name=decl.name)
            decl = SymbolDeclaration(annotations='', name=symb,
                                        sorts=[TYPE(name=A_Tname)],
                                        out=TYPE(name=BOOL))
            decl.lift = True
            decl.annotate(voc)
            pre_declarations[decl.name] = decl

        th.declarations = {**pre_declarations, **th.declarations}

        th._uninterpreted_types = [
            pre_declarations[f"{decl.name}_T"]
            for decl in th._uninterpreted_types
        ]

    todo = {}
    if lift:

        # create mul symbol for each type
        for decl in th._uninterpreted_types:
            # mul_T: T -> Int
            mul = _mul(decl.base_type.name)
            symb_decl = SymbolDeclaration(annotations='', name=mul,
                                        sorts=[TYPE(name=decl.base_type.name)],
                                        out=TYPE(name=INT))
            symb_decl.lift = True
            symb_decl.block = voc
            symb_decl.annotate(voc)
            mul.decl = symb_decl
            th.declarations[mul.name] = symb_decl

            if not monotype:
                # !x in A_T: A(x) <=> 0 < mul_AT(x).
                new_constraint = (f"! x in {decl.name}: "
                        f"{decl.name[:-2]}(x) "
                        f"<=> 0 < mul{decl.name}(x)."
                    )
                new_constraints.append(new_constraint)

        # transform original definitions
        th.definitions = []
        for defn in self.definitions:
            new_defn = copy(defn)
            new_defn.canonicals = {}
            for decl, rules in defn.canonicals.items():
                new_rules = []
                for r in rules:
                    new_r = copy(r)
                    new_r.definiendum = lift_expr(new_r.definiendum, th, voc, todo)
                    new_r.body = lift_expr(new_r.body, th, voc, todo)
                    new_rules.append(new_r)
                new_defn.canonicals[decl] = new_rules
            th.definitions.append(new_defn)

        # transform original constraints
        th.constraints = OrderedSet()
        for axiom in self.constraints.values():
            try:
                new = lift_expr(axiom, th, voc, todo)
                new.annotations['concrete'] = axiom.str
            except Exception as e:
                new = TRUE
                new.annotations['concrete'] = f"{str(e)}{NEWL}      // {axiom.str}"
            th.constraints.append(new)
        # add constraints on mul and cardinality
        new_constraints.extend(add_constraints(th, voc, todo))

    def render_c(c):
        if 'concrete' in c.annotations:
            return f"[{c.annotations['concrete']}]{NEWL}      {c.code}."
        else:
            return f"{c.code}."

    def render_d(d):
        return (f"{{ "
                f"{f'NEWL      '.join(str(r)+f'.{NEWL}' for rules in d.canonicals.values() for r in rules)}"
                f"    }}")

    the = (f"theory T:V {{ {NEWL}    "
            f"{f'{NEWL}    '.join(render_c(c) for c in th.constraints)}{NEWL}    "
            f"{f'{NEWL}    '.join(render_d(d) for d in th.definitions)}{NEWL}    "
            f"{new_definition}"
            f"{f'{NEWL}    '.join(d for d in new_constraints)}{NEWL}    "
            f"{f'{NEWL}    '.join(str(i)+'.' for i in self.interpretations.values() if type(i.block)!=Vocabulary)}{NEWL}"
            f"}}{NEWL}")

    vocabulary = (f"vocabulary V {{ {NEWL}"
            f"    {f'{NEWL}    '.join(str(d) for d in th.declarations.values())}{NEWL}"
            f"    {f'{NEWL}    '.join(str(d) for d in new_symbols.values())}{NEWL}"
            f"}}{NEWL}")
    vocabulary = vocabulary.replace("    \n", "")
    source = vocabulary + the

    voc.symbol_decls, new_symbol_decls = new_symbol_decls, voc.symbol_decls
    return source


def _vars_of(quantees: List[Quantee], voc):
    """ returns a dict of variables in quantees
    """
    out = {var.name: var.annotate(voc, {}) for q in quantees for vars in q.vars for var in vars}
    assert len(out) == len(set(out)), f"Repetition of variables in {quantees}"
    return out

def _mul(type_name: str):
    """return the Symbol for mul_T
    """
    return SYMBOL(name=f"mul{type_name}")

def _base_type(sort, theory):
    "returns the base_type of sort, or None if it is interpreted"
    base_type = theory.declarations[sort.name].base_type
    base_type = theory.declarations[base_type.name].base_type  # in case of ConfigObject
    return (base_type if any(base_type.name == decl.name
                             for decl in theory._uninterpreted_types) else
            None)

def _MUL(vars, theory):
    """ returns the product of the multiplicity of the variables,
    by looking at their base type
    """
    out = []
    for var in vars.values():
        base_type = _base_type(var.sort, theory)
        if base_type:
            symb = _mul(base_type.name)
            out.append(AppliedSymbol.make(symb, [var]))
    if len(out) == 0:
        return ONE
    if len(out) == 1:
        return out[0]
    return AMultDiv.make('*', out)


def _check_guard(expr: Expression, theory, voc, todo, q_vars):
    """detects the presence of `t(xs)=y` in the inner expression of a quantification

    Args:
        expr (Expression): a quantification or aggregate

    Returns:
        xs (Dict): the variables being quantified
        ys (Dict): the free variable in `expr`
        divide (Bool): True if the guard is `f(xs)=y`

    """
    xs, f = _vars_of(expr.quantees, voc), expr.sub_exprs[0]
    ys = {k for k in f.variables if k not in xs}
    ys_ = {k: v for k,v in q_vars.items() if k in ys}  # ys resolved
    Txs = sorted([_base_type(x.sort, theory).name for x in xs.values()
                    if _base_type(x.sort, theory) is not None])
    Tys = sorted([_base_type(y.sort, theory).name for y in ys_.values()
                    if _base_type(y.sort, theory) is not None])

    q = expr.q if type(expr) == AQuantification else expr.aggtype

    divide = False
    if len(ys) == 1:  # try to find the guard
        guard = None
        if (type(f) == AComparison and len(f.sub_exprs) == 1
        and q != '∀' and f.operator[0] == "="):
                # ?xs: f(xs)=y  -->  ?xs: lift_expr(f(xs)=y)
                guard = f
        elif (q == '∀' and type(f) == AUnary and type(f.sub_exprs[0]) == AComparison
        and len(f.sub_exprs[0].sub_exprs) == 1 and f.sub_exprs[0].operator[0] == "="):
            # !xs: f(xs) ~= y
            guard = f.sub_exprs[0]
        elif ((q == '∀' and type(f) == AImplication)
        or (q in ['∃', '#'] and type(f) == AConjunction)):
            # !xs: f(xs)=y => phi(xs,y)  -->  !xs: f(xs)=y => lift_expr(phi(xs,y))
            # ?xs: f(xs)=y &  phi(xs,y)  -->  ?xs: f(x)=y & lift_expr(phi(xs,y))
            guard = f.sub_exprs[0]
        elif q in ['#'] and type(f) == AIfExpr:
            guard = f.sub_exprs[0]
            if type(guard) == AConjunction:
                guard = guard.sub_exprs[0]

        # if t(xs)=y
        if (type(guard) == AComparison
        and guard.sub_exprs[0].variables == set(xs.keys())
        and guard.sub_exprs[1].variables == ys
        and len(ys) == 1):
            if (type(guard.sub_exprs[0]) == AppliedSymbol
            and all(type(e) == Variable for e in guard.sub_exprs[0].sub_exprs)
            and type(guard.sub_exprs[1]) == Variable):
                # share todo with function declaration
                todo.setdefault((str(Txs), guard.sub_exprs[0].decl.name), (xs, ys_, guard.sub_exprs[0]))
            else:
                todo.setdefault((str(Txs), guard.sub_exprs[0].str), (xs, ys_, guard.sub_exprs[0]))
            divide = True
    if not divide:  # add LCM condition for xs+ys
        xys = {**xs, **ys_}
        Txs = sorted(Txs + Tys)
        todo.setdefault((str(Txs), None), (xys, None, None))

    return (xs, ys_, divide)


def _has_card_(e, theory, voc, todo, q_vars):  # recursive for +, -, bracket
    if type(e) == AAggregate:
        _, _, divide = _check_guard(e, theory, voc, todo, q_vars)
        return divide
    if type(e) in [AUnary, ASumMinus, AMultDiv, Brackets]:
        return any(_has_card_(e1, theory, voc, todo, q_vars) for e1 in e.sub_exprs)
    return False


def lift_expr(expr: Expression, theory, voc, todo, q_vars=None) -> Expression:
    """ returns a lifted version of expr

    Args:
        expr (Expression): the concrete sentence
        theory (Theory): the concrete theory (with _uninterpreted_types)
        voc (Vocabulary): the vocabulary of the sentence
        todo:
        q_vars (dict, optional): the variables available in the current scope.
            Needed to resolve names in Expression.variables.  Defaults to empty.

    Returns:
        Expression: the lifted sentence
    """
    q_vars = {} if q_vars is None else q_vars
    if expr.same_as(TRUE) or expr.same_as(FALSE):
        return expr

    if type(expr) == AppliedSymbol:
        if len(expr.sub_exprs) == 0:  # p()  -->  p()
            return expr
        # p(t)  -->  p(lift_term(t))
        out = deepcopy(expr).update_exprs([
            lift_term(term, theory, voc, todo, q_vars)
            for term in expr.sub_exprs])
        out.code = out.str
        return out

    elif type(expr) == AComparison:
        # t1(x) = t2()  --> X(t1()) = X(t2())
        # #{xs: t(xs)=y & phi(xs,y)} = t(y) --> multiply both terms by mul(y)
        # #{xs: t(xs)=y1 & phi(xs,y)} = #{xs: t(xs)=y2 & phi(xs,2)} --> multiply both terms by mul(y1, y2)

        has_divider = any(_has_card_(e1, theory, voc, todo, q_vars)
                          for e1 in expr.sub_exprs)
        mul_vars = ({} if not has_divider else
                    {k:v for k,v in q_vars.items() if k in expr.variables})
        out = deepcopy(expr).update_exprs([
            lift_term(term, theory, voc, todo, q_vars, mul_vars)
            for term in expr.sub_exprs])
        out.code = out.str
        return out

    elif type(expr) in [AUnary, Brackets, AImplication, AConjunction, ADisjunction, AEquivalence, AIfExpr]:
        # phi(x)  --> lift_expr(phi(x))
        out = deepcopy(expr).update_exprs([
            lift_expr(e, theory, voc, todo, q_vars) for e in expr.sub_exprs
        ])
        out.code = out.str
        return out

    elif type(expr) == AQuantification:
        assert len(expr.sub_exprs) == 1, "Internal error: quantification is already expanded !"

        xs, _, _ = _check_guard(expr, theory, voc, todo, q_vars)
        xs.update(q_vars)
        out = lift_expr(expr.f, theory, voc, todo, xs)
        if expr.q == '∀':
            return FORALL(expr.quantees, out).annotate(voc, {})
        elif expr.q == '∃':
            return EXISTS(expr.quantees, out).annotate(voc, {})

    assert False, f"Lifting of {expr} is not supported"


def lift_term(term: Expression,
              theory,
              voc: Vocabulary,
              todo,
              q_vars,
              mul_vars = None) -> Expression:
    """ transform a term, and multiply the result by mul(mul_vars) if any (for performance)

    Args:
        term (Expression): the term to be lifted
        theory (Theory): the concrete theory (with _uninterpreted_types)
        voc (Vocabulary): vocabulary used for annotations
        todo:
        q_vars (dict, optional): the variables available in the current scope. Defaults to empty.
        mul_vars {dict, optional}: the variables used to multiply the lifted term

    Returns:
        Expression: the lifted term
    """
    mul_vars = {} if mul_vars is None else mul_vars
    if type(term) == AAggregate:
        # #{xs: phi(xs)} --> sum(lambda xs: if lift_expr(phi(xs)) then mul(xs) else 0)
        # #{xs: f(xs)=y & phi(y, xs)} -->
        #          sum(lambda xs: if f(xs)=y & lift_expr(phi(y,xs)) then mul(xs) / mul(y) else 0)
        # multiply by mul(mul_vars\{y})
        xs, y_, divide = _check_guard(term, theory, voc, todo, q_vars)
        THEN = _MUL(xs, theory)
        xy = {**xs, **y_}

        if term.aggtype == '#':
            phi = lift_expr(term.f, theory, voc, {}, xy)
            new_term = IF(phi, THEN, ZERO, phi.annotations)
        elif term.aggtype == 'sum':
            x_term = lift_term(term.f, theory, voc, {}, xy)
            new_term = AMultDiv.make("*", [THEN, x_term])
        else:
            assert False, f"{term.aggtype} aggregate is not supported"

        out = AAggregate(None,
                         aggtype='sum',
                         quantees=term.quantees,
                         f=new_term).annotate(voc, {})
        if divide:
            assert len(y_) == 1, "Internal error"
            if mul_vars:  # multiply by mul(mul_vars\{y})
                assert all(y in mul_vars for y in y_), "Internal error"
                mul_vars = {k:v for k,v in mul_vars.items() if k not in y_}
            else:  # divide by mul(y_)
                out = AMultDiv.make("/", [out, _MUL(y_, theory)])
                mul_vars = {}  # do not multiply again
        # else multiply by mul_vars
    elif type(term) in [Number, UnappliedSymbol, Variable]:  # n, ID, x --> n, ID, x
        out = term
    elif type(term) == AppliedSymbol:
        out = deepcopy(term).update_exprs([
            lift_term(e, theory, voc, todo, q_vars, {})
            for e in term.sub_exprs])
    elif type(term) in [AUnary, ASumMinus, Brackets]:
        out = deepcopy(term).update_exprs([
            lift_term(e, theory, voc, todo, q_vars,
                      {} if type(term) == AppliedSymbol else mul_vars)
            for e in term.sub_exprs])
        mul_vars = {}  # do not multiply again
    elif type(term) == AIfExpr:
        out = deepcopy(term).update_exprs([
            lift_expr(term.sub_exprs[0], theory, voc, todo, q_vars),
            lift_term(term.sub_exprs[1], theory, voc, todo, q_vars, mul_vars),
            lift_term(term.sub_exprs[2], theory, voc, todo, q_vars, mul_vars)])
        mul_vars = {}  # do not multiply again
    elif type(term) == AMultDiv and all(op=="⨯" for op in term.operator):
        out, new  = deepcopy(term), []
        for e in out.sub_exprs:
            if _has_card_(e, theory, voc, todo, q_vars):
                free_vars = {k:v for k,v in q_vars.items() if k in e.variables}
                new.append(lift_term(e, theory, voc, todo, q_vars, free_vars))
                mul_vars = {k:v for k,v in mul_vars.items() if k not in free_vars}
            else:
                new.append(lift_term(e, theory, voc, todo, q_vars, {}))
        out.update_exprs(new)
    else:
        assert False, f"Lifting of {term} ({type(term)}) is not supported"

    if mul_vars:
        out = AMultDiv.make("*", [out, _MUL(mul_vars, theory)])
    return out


def _totality_constraint(vars: Dict[str, Variable],
                         theory: "Theory"
                        ) -> Optional[str]:
    """creates the totality constraint for vars,
    and adds it to theory or returns it as a string

    Args:
        vars (Dict[str, Variable]): the variables and their type
        theory (Theory): the lifted theory

    Returns:
       str: the totality constraint
    """
    if len(vars) == 2:  # binary condition
        v1, v2 = [v for v in vars.values()]
        mul_v1, mul_v2 = _MUL({v1.name:v1}, theory), _MUL({v2.name:v2}, theory)
        return (f"∀ {v1} ∈ {v1.sort}, {v2} ∈ {v2.sort}: "
                f"∀ n, m ∈ Int: 0 < n < {mul_v1} ∧ 0 < m < {mul_v2}"
                f" ⇒ {mul_v1} * m ≠ {mul_v2} * n.")

    # simplification of LCM condition -> max one lifted type in the domain
    # !xs: If(1<mul(x1), 1, 0) + ... =< 1
    terms = [AIfExpr.make(AComparison.make('<', [ONE, _MUL({x1.name:x1}, theory)]),
                            ONE, ZERO)
                for x1 in vars.values()
                if _MUL({x1.name:x1}, theory) != 1]
    if terms:
        expr = AComparison.make('≤', [ASumMinus.make('+', terms), ONE])

        for x1 in vars.values():
            expr = FORALL([Quantee.make(x1, x1.sort)], expr)
        theory.constraints.append(expr)
        return None


def add_constraints(theory, voc: Vocabulary, todo) -> List[str]:
    new_constraints = []
    for decl in theory.declarations.values():
        symb = SYMBOL(name=decl.name)
        if decl.lift and re.match("mul\w", decl.name):
            # ! x in T: 0 =< mul(x)
            x = VARIABLE(name=f"{decl.name}0_", sort=decl.sorts[0])
            app = AppliedSymbol.make(symb, [x])
            eq = AComparison.make("≤", [ZERO, app])
            quantees = [Quantee.make(x, decl.sorts[0])]
            constr = FORALL(quantees, eq)
            theory.constraints.append(constr.annotate(voc, {}))

        if type(decl) == SymbolDeclaration:
            xs = {f"{decl.name}{i}_": VARIABLE(name=f"{decl.name}{i}_", sort=s)
                for i,s in enumerate(decl.sorts)}
            y = {decl.out.name : VARIABLE(name=f"{decl.name}_", sort=decl.out)}

            if (any(_base_type(x.sort,  theory) for x  in xs.values())
            or  any(_base_type(y0.sort, theory) for y0 in y.values())):
                Ts = sorted([_base_type(s, theory).name for s in decl.sorts
                             if _base_type(s, theory)])
                if decl.out.name != BOOL:  # a function symbol
                    muly = _MUL(y, theory)
                    if muly != ONE:  # y may not be concrete
                        symb = SYMBOL(name=decl.name)
                        term = AppliedSymbol.make(symb, xs.values())
                        todo.setdefault((str(Ts), decl.name), (xs, y, term))
                    elif 1 < decl.arity:  # binary function
                        # no need to generate the "n" condition
                        todo.setdefault((str(Ts), None), (xs, None, None))
                elif 1 < decl.arity:  # binary predicate
                    todo.setdefault((str(Ts), None), (xs, None, None))
                # else: pass

    for (xs, y, term) in todo.values():
        # ! xs: LCM(xs) = MUL(xs)
        if 1 < len(xs):
            expr = _totality_constraint(xs, theory)
            if expr:
                new_constraints.append(expr)
        if term:  # a term using xs, with the type of y
            # f(xs)  --> !xs: ?n: mul(xs) = n * mul(term)
            # c()    --> mul(term) = 1
            muly = _MUL(y, theory)  # f"mul{base_type}(y)"
            if not muly.same_as(ONE):
                mulfxs = AppliedSymbol.make(muly.symbol, [term])
                mulxs = _MUL(xs, theory)
                if mulxs.same_as(ONE):
                    expr = EQUALS([mulfxs, ONE])
                else:
                    var_n = VARIABLE(name="n__5sldkqsdf",  # in case n is used in the term
                                    sort=theory.declarations[muly.symbol.name].out)  # INT
                    n = UnappliedSymbol(None, s=SYMBOL(name="n")).annotate(voc, {"n": var_n})
                    prod = AMultDiv.make("*", [n, mulfxs])
                    eq = EQUALS([mulxs, prod])
                    INTsymb = SymbolExpr(None, s=SYMBOL(name=INT)).annotate(voc, {})
                    expr = EXISTS([Quantee.make(var_n, sort=INTsymb)], eq)
                for x in xs.values():
                    expr = FORALL([Quantee.make(x, x.sort)], expr)

                theory.constraints.append(expr)
    # new_constraints.append("true.")
    return new_constraints
