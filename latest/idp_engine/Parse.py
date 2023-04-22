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

Classes to parse an IDP-Z3 theory.

"""
from __future__ import annotations

from copy import copy, deepcopy
from datetime import date
from enum import Enum
from itertools import groupby
from os import path
from re import match
from sys import intern
from textx import metamodel_from_file
from typing import Dict, List, Union, Optional


from .Assignments import Assignments
from .Expression import (Annotations, ASTNode, Constructor, CONSTRUCTOR, Accessor,
    Symbol, SYMBOL, SymbolExpr, Expression, AIfExpr, IF, AQuantification,
    Type, TYPE, Quantee, ARImplication, AEquivalence,
    AImplication, ADisjunction, AConjunction,
    AComparison, ASumMinus, AMultDiv, APower, AUnary,
    AAggregate, AppliedSymbol, UnappliedSymbol,
    Number, Brackets, Date, Extension,
    Variable, TRUEC, FALSEC, TRUE, FALSE, EQUALS, AND, OR, EQUIV)
from .utils import (RESERVED_SYMBOLS, OrderedSet, NEWL, BOOL, INT, REAL, DATE, CONCEPT,
    GOAL_SYMBOL, EXPAND, RELEVANT, ABS, IDPZ3Error,
    CO_CONSTR_RECURSION_DEPTH, MAX_QUANTIFIER_EXPANSION,
    Semantics as S)


def str_to_IDP(atom, val_string):
    """cast a string value for 'atom into an Expr object, or None

    used to convert Z3 models or json data from GUI

    Args:
        atom (Expr): the atom whose value must be converted
        val_string (str): the string representation of the value

    Returns:
        Expr?: the value cast as Expr, or None if unknown
    """
    assert atom.type, "Internal error"
    if val_string == str(atom) or val_string+"()" == str(atom):
        out = None  # Z3 means the value is unknown
    elif atom.type == BOOL:
        if val_string not in ['True', 'False', 'true', 'false']:
            raise IDPZ3Error(
                f"{atom.annotations['reading']} has wrong value: {val_string}")
        out = (TRUE if val_string in ['True', 'true'] else
               FALSE)
    elif atom.type == DATE:
        d = (date.fromordinal(eval(val_string)) if not val_string.startswith('#') else
             date.fromisoformat(val_string[1:]))
        out = Date(iso=f"#{d.isoformat()}")
    elif (hasattr(atom.decl.out.decl.base_type, 'map')
          and val_string in atom.decl.out.decl.base_type.map):  # constructor
        out = atom.decl.out.decl.base_type.map[val_string]
    elif 1 < len(val_string.split('(')):  # e.g., pos(0,0)
        # deconstruct val_string
        m = match(r"(?P<function>\w+)\s?\((?P<args>(?P<arg>\w+(,\s?)?)+)\)",
                  val_string).groupdict()

        typ = atom.decl.out.decl
        assert hasattr(typ, 'interpretation'), "Internal error"
        constructor = next(c for c in typ.interpretation.enumeration.constructors
                           if c.name == m['function'])

        args = m['args'].split(',')
        args = [Number(number=str(eval(a.replace('?', ''))))  #TODO deal with any argument based on constructor signature
                for a in args]

        out = AppliedSymbol.construct(constructor, args)
    elif atom.type == REAL:  # Z3 adds a '?' when the real number is rounded
        out = Number(number= val_string if '/' in val_string else
                     str(float(eval(val_string.replace('?', '')))))
    else:  # an Int
        out = Number(number=str(eval(val_string)))
    return out


class ViewType(Enum):
    HIDDEN = "hidden"
    NORMAL = "normal"
    EXPANDED = "expanded"


class IDP(ASTNode):
    """The class of AST nodes representing an IDP-Z3 program.
    """
    """ do not display this info in the API
    Attributes:
        code (str): source code of the IDP program

        vocabularies (Dict[str, Vocabulary]): list of vocabulary blocks, by name

        theories (Dict[str, TheoryBlock]): list of theory blocks, by name

        structures (Dict[str, Structure]): list of structure blocks, by name

        procedures (Dict[str, Procedure]): list of procedure blocks, by name

        display (Display, Optional): display block, if any
    """
    def __init__(self, **kwargs):
        # log("parsing done")
        self.code = None
        self.vocabularies = self.dedup_nodes(kwargs, 'vocabularies')
        self.theories = self.dedup_nodes(kwargs, 'theories')
        self.structures = self.dedup_nodes(kwargs, 'structures')
        displays = kwargs.pop('displays')
        self.procedures = self.dedup_nodes(kwargs, 'procedures')

        assert len(displays) <= 1, "Too many display blocks"
        self.display = displays[0] if len(displays) == 1 else None

        for voc in self.vocabularies.values():
            voc.annotate(self)
        for t in self.theories.values():
            t.annotate(self)
        for struct in self.structures.values():
            struct.annotate(self)

        # determine default vocabulary, theory, before annotating display
        self.vocabulary = next(iter(self.vocabularies.values()))
        self.theory = next(iter(self.theories    .values()))
        if self.display is None:
            self.display = Display(constraints=[], interpretations=[])

    @classmethod
    def from_file(cls, file:str) -> "IDP":
        """parse an IDP program from file

        Args:
            file (str): path to the source file

        Returns:
            IDP: the result of parsing the IDP program
        """
        assert path.exists(file), f"Can't find {file}"
        with open(file, "r") as source:
            code = source.read()
            return cls.from_str(code)

    @classmethod
    def from_str(cls, code:str) -> "IDP":
        """parse an IDP program

        Args:
            code (str): source code to be parsed

        Returns:
            IDP: the result of parsing the IDP program
        """
        out = idpparser.model_from_str(code)
        out.code = code
        return out

    @classmethod
    def parse(cls, file_or_string: str) -> "IDP":
        """DEPRECATED: parse an IDP program

        Args:
            file_or_string (str): path to the source file, or the source code itself

        Returns:
            IDP: the result of parsing the IDP program
        """
        print("IDP.parse() is deprecated. Use `from_file` or `from_str` instead")
        code = file_or_string
        if path.exists(file_or_string):
            with open(file_or_string, "r") as source:
                code = source.read()
        out = idpparser.model_from_str(code)
        out.code = code
        return out

    def get_blocks(self, blocks: List[str]) -> List[ASTNode]:
        """returns the AST nodes for the blocks whose names are given

        Args:
            blocks (List[str]): list of names of the blocks to retrieve

        Returns:
            List[Union[Vocabulary, TheoryBlock, Structure, Procedure, Display]]:
                list of AST nodes
        """
        names = blocks.split(",") if type(blocks) is str else blocks
        out = []
        for name in names:
            name = name.strip()  # remove spaces
            out.append(self.vocabularies[name] if name in self.vocabularies else
                       self.theories[name] if name in self.theories else
                       self.structures[name] if name in self.structures else
                       self.procedures[name] if name in self.procedures else
                       self.display if name == "Display" else
                       "")
        return out

    def execute(self) -> None:
        pass  # monkey patched


################################ Vocabulary  ##############################


class Vocabulary(ASTNode):
    """The class of AST nodes representing a vocabulary block.
    """
    def __init__(self, **kwargs):
        self.name = kwargs.pop('name')
        self.declarations = kwargs.pop('declarations')
        self.idp = None  # parent object
        self.symbol_decls: Dict[str, Declaration] = {}

        self.name = 'V' if not self.name else self.name
        self.voc = self

        # expand multi-symbol declarations
        temp = []
        for decl in self.declarations:
            if not isinstance(decl, SymbolDeclaration):
                decl.private = decl.name.startswith('_')
                temp.append(decl)
            else:
                for symbol in decl.symbols:
                    new = copy(decl)  # shallow copy !
                    new.name = intern(symbol.name)
                    new.private = new.name.startswith('_')
                    new.symbols = None
                    temp.append(new)
        self.declarations = temp

        # define built-in types: Bool, Int, Real, Symbols
        self.declarations = [
            TypeDeclaration(
                name=BOOL, constructors=[TRUEC, FALSEC]),
            TypeDeclaration(name=INT, enumeration=IntRange()),
            TypeDeclaration(name=REAL, enumeration=RealRange()),
            TypeDeclaration(name=DATE, enumeration=DateRange()),
            TypeDeclaration(
                name=CONCEPT,
                constructors=[]),
            SymbolDeclaration(annotations='', name=SYMBOL(GOAL_SYMBOL),
                              sorts=[TYPE(CONCEPT, ins=[],
                                             out=TYPE(BOOL))],
                              out=TYPE(BOOL)),
            SymbolDeclaration(annotations='', name=SYMBOL(RELEVANT),
                              sorts=[TYPE(CONCEPT, ins=[],
                                             out=TYPE(BOOL))],
                              out=TYPE(BOOL)),
            SymbolDeclaration(annotations='', name=SYMBOL(ABS),
                                sorts=[TYPE(INT)],
                                out=TYPE(INT)),
            ] + self.declarations

    def __str__(self):
        return (f"vocabulary {{{NEWL}"
                f"    {f'{NEWL}    '.join(str(i) for i in self.declarations)}"
                f"{NEWL}}}{NEWL}").replace("    \n", "")

    def add_voc_to_block(self, block):
        """adds the enumerations in a vocabulary to a theory or structure block

        Args:
            block (Theory): the block to be updated
        """
        for s in self.declarations:
            block.check(s.name not in block.declarations,
                        f"Duplicate declaration of {self.name} "
                        f"in vocabulary and block {block.name}")
            block.declarations[s.name] = s
            if (type(s) == TypeDeclaration
                and s.interpretation
                and self.name != BOOL):
                block.check(s.name not in block.interpretations,
                            f"Duplicate enumeration of {self.name} "
                            f"in vocabulary and block {block.name}")
                block.interpretations[s.name] = s.interpretation


class Import(ASTNode):
    def __init__(self, **kwargs):
        self.name = kwargs.pop('name')

    def __str__(self):
        return f"Import {self.name}"


class TypeDeclaration(ASTNode):
    """AST node to represent `type <symbol> := <enumeration>`

    Args:
        name (string): name of the type

        arity (int): the number of arguments

        sorts (List[Symbol]): the types of the arguments

        out (Symbol): the Boolean Symbol

        type (string): Z3 type of an element of the type; same as `name`

        base_type : self

        constructors ([Constructor]): list of constructors in the enumeration

        interpretation (SymbolInterpretation): the symbol interpretation

        map (Dict[string, Expression]): a mapping from code to Expression in range

        voc (Vocabulary): the vocabulary block that contains it

        lift (bool): whether it is part of a lifted vocabulary
    """

    def __init__(self, **kwargs):
        self.name = kwargs.pop('name')
        self.constructors = ([] if 'constructors' not in kwargs else
                             kwargs.pop('constructors'))
        enumeration = (None if 'enumeration' not in kwargs else
                            kwargs.pop('enumeration'))

        self.arity = 1
        self.sorts = [SYMBOL(self.name)]
        self.out = SYMBOL(BOOL)
        self.type = (self.name if type(enumeration) != Ranges else
                     enumeration.type)  # INT or REAL or DATE
        self.base_type = self
        self.lift = False

        self.map = {}  # {String: constructor}

        self.interpretation = (None if enumeration is None else
            SymbolInterpretation(name=SYMBOL(self.name), sign='≜',
                                 enumeration=enumeration, default=None))

    def __str__(self):
        if self.name in RESERVED_SYMBOLS:
            return ''
        enumeration = self.enumeration if hasattr(self, 'enumeration') and self.enumeration else ""
        constructors = enumeration.constructors if enumeration else None
        constructed = ("" if not bool(constructors) or all(0 == len(c.sorts) for c in constructors)
                       else "constructed from ")
        enumeration = (f"{constructed}{{{', '.join(str(c) for c in constructors)}}}" if constructors else
                       f"{self.interpretation}" if self.interpretation else
                       f"{enumeration}")
        return (f"type {self.name} {'' if not enumeration else ':= ' + enumeration}")

    def contains_element(self, term: Expression,
                     interpretations: Dict[str, "SymbolInterpretation"],
                     extensions: Dict[str, Extension]
                     ) -> Expression:
        """returns an Expression that is TRUE when `term` is in the type
        """
        if self.name == CONCEPT:
            comparisons = [EQUALS([term, UnappliedSymbol.construct(c)])
                          for c in self.constructors]
            return OR(comparisons)
        else:
            (superset, filter) = extensions[self.name]
            if superset is not None:
                # superset.sort(key=lambda t: str(t))
                comparisons = [EQUALS([term, t[0]]) for t in superset]
                out = (OR(comparisons) if filter is None else
                       AND([filter([term]), OR(comparisons)]))
            elif filter is not None:
                out = filter([term])
            else:
                out = TRUE
            return out


class SymbolDeclaration(ASTNode):
    """The class of AST nodes representing an entry in the vocabulary,
    declaring one or more symbols.
    Multi-symbols declaration are replaced by single-symbol declarations
    before the annotate() stage.

    Attributes:
        annotations : the annotations given by the expert.

            `annotations['reading']` is the annotation
            giving the intended meaning of the expression (in English).

        symbols ([Symbol]): the symbols being defined, before expansion

        name (string): the identifier of the symbol, after expansion of the node

        arity (int): the number of arguments

        sorts (List[Symbol]): the types of the arguments

        out (Symbol): the type of the symbol

        type (string): name of the Z3 type of an instance of the symbol

        base_type (TypeDeclaration): base type of the unary predicate (None otherwise)

        instances (Dict[string, Expression]):
            a mapping from the code of a symbol applied to a tuple of
            arguments to its parsed AST

        range (List[Expression]): the list of possible values

        private (Bool): True if the symbol name starts with '_' (for use in IC)

        unit (str):
            the unit of the symbol, such as m (meters)

        heading (str):
            the heading that the symbol should belong to

        optimizable (bool):
            whether this symbol should get optimize buttons in the IC

        needs_interpretation (bool):
            whether its interpretation must be sent to Z3

        voc (Vocabulary): the vocabulary block that contains it

        lift (bool): whether it is part of a lifted vocabulary
    """

    def __init__(self, **kwargs):
        self.annotations = kwargs.pop('annotations')
        if 'symbols' in kwargs:
            self.symbols = kwargs.pop('symbols')
            self.name = None
        else:
            self.symbols = None
            if 'name' in kwargs:
                self.name = intern(kwargs.pop('name').name)
            else:
                self.name = intern(kwargs.pop('strname'))
        self.sorts = kwargs.pop('sorts')
        self.out = kwargs.pop('out')
        if self.out is None:
            self.out = SYMBOL(BOOL)

        self.arity = len(self.sorts)
        self.annotations = self.annotations.annotations if self.annotations else {}
        self.private = None
        self.unit: str = None
        self.heading: str = None
        self.optimizable: bool = True
        self.lift = False
        self.needs_interpretation = False

        self.type = None  # a string
        self.base_type = None
        self.range = None  # all possible values.  Used in get_range and IO.py
        self.instances = None  # {string: AppliedSymbol} not starting with '_'
        self.block: Optional[Block] = None  # vocabulary where it is declared
        self.view = ViewType.NORMAL  # "hidden" | "normal" | "expanded" whether the symbol box should show atoms that contain that symbol, by default

    @classmethod
    def make(cls, strname, arity, sorts, out):
        o = cls(strname=strname, arity=arity, sorts=sorts, out=out, annotations={})
        return o

    def __str__(self):
        if self.name in RESERVED_SYMBOLS:
            return ''
        args = '⨯'.join(map(str, self.sorts)) if 0 < len(self.sorts) else ''
        return (f"{self.name}: "
                f"{ '('+args+')' if args else '()'}"
                f" → {self.out.name}")

    def __repr__(self):
        return str(self)

    def has_in_domain(self, args: List[Expression],
                      interpretations: Dict[str, "SymbolInterpretation"],
                      extensions: Dict[str, Extension]
                      ) -> Expression:
        """Returns an expression that is TRUE when `args` are in the domain of the symbol.

        Arguments:
            args (List[Expression]): the list of arguments to be checked, e.g. `[1, 2]`

        Returns:
            Expression: whether `(1,2)` is in the domain of the symbol
        """
        assert len(self.sorts) == len(args), \
            f"Incorrect arity of {str(args)} for {self.name}"
        return AND([typ.has_element(term, interpretations, extensions)
                   for typ, term in zip(self.sorts, args)])

    def has_in_range(self, value: Expression,
                     interpretations: Dict[str, "SymbolInterpretation"],
                     extensions: Dict[str, Extension]
                     ) -> Expression:
        """Returns an expression that says whether `value` is in the range of the symbol.
        """
        return self.out.has_element(value, interpretations, extensions)

    def contains_element(self, term: Expression,
                     interpretations: Dict[str, "SymbolInterpretation"],
                     extensions: Dict[str, Extension]
                     ) -> Expression:
        """returns an Expression that is TRUE when `term` satisfies the predicate
        """
        assert self.type == BOOL, "Internal error"
        (superset, filter) = extensions[self.name]
        if superset is not None:
            # superset.sort(key=lambda t: str(t))
            comparisons = [EQUALS([term, t[0]]) for t in superset]
            out = (OR(comparisons) if filter is None else
                    AND([filter([term]), OR(comparisons)]))
        elif filter is not None:
            out = filter([term])
        else:
            out = TRUE
        return out

class VarDeclaration(ASTNode):
    """ represents a declaration of variable (IEP 24)

    Attributes:
        name (str): name of the variable

        subtype (Type): type of the variable

        lift (bool): whether it is part of a lifted vocabulary
    """

    def __init__(self, **kwargs):
        self.name = kwargs.pop('name').name
        self.subtype = kwargs.pop('subtype')
        self.lift = False

    def __str__(self):
        return f"var {self.name} ∈ {self.subtype}"

Declaration = Union[TypeDeclaration, SymbolDeclaration]


################################ TheoryBlock  ###############################


class TheoryBlock(ASTNode):
    """ The class of AST nodes representing a theory block.
    """
    def __init__(self, **kwargs):
        self.name = kwargs.pop('name')
        self.vocab_name = kwargs.pop('vocab_name')
        constraints = kwargs.pop('constraints')
        self.definitions = kwargs.pop('definitions')
        self.interpretations = self.dedup_nodes(kwargs, 'interpretations')

        self.name = "T" if not self.name else self.name
        self.vocab_name = 'V' if not self.vocab_name else self.vocab_name

        self.declarations = {}
        self.def_constraints = {}  # {(Declaration, Definition): List[Expression]}
        self.assignments = Assignments()

        self.constraints = OrderedSet()
        for c in constraints:
            c.block = self
            if c.annotations is not None:
                c.expr.annotations = c.annotations.annotations
            self.constraints.append(c.expr)
        for definition in self.definitions:
            for rule in definition.rules:
                rule.block = self

    def __str__(self):
        return self.name


class Definition(ASTNode):
    """ The class of AST nodes representing an inductive definition.
        id (num): unique identifier for each definition

        rules ([Rule]):
            set of rules for the definition, e.g., `!x: p(x) <- q(x)`

        canonicals (Dict[Declaration, List[Rule]]):
            normalized rule for each defined symbol,
            e.g., `!$p!1$: p($p!1$) <- q($p!1$)`

        instantiables (Dict[Declaration], List[Expression]):
            list of instantiable expressions for each symbol,
            e.g., `p($p!1$) <=> q($p!1$)`

        clarks (Dict[Declaration, Transformed Rule]):
            normalized rule for each defined symbol (used to be Clark completion)
            e.g., `!$p!1$: p($p!1$) <=> q($p!1$)`

        def_vars (Dict[String, Dict[String, Variable]]):
            Fresh variables for arguments and result

        level_symbols (Dict[SymbolDeclaration, Symbol]):
            map of recursively defined symbols to level mapping symbols

        cache (Dict[SymbolDeclaration, str, Expression]):
            cache of instantiation of the definition

        inst_def_level (int): depth of recursion during instantiation

    """
    definition_id = 0  # intentional static variable so that no two definitions get the same ID

    def __init__(self, parent, annotations, mode, rules):
        Definition.definition_id += 1
        self.id = Definition.definition_id
        self.mode = (S.WELLFOUNDED if mode is None or 'well-founded' in mode else
                     S.COMPLETION if 'completion' in mode else
                     S.KRIPKEKLEENE if 'Kripke-Kleene' in mode else
                     S.COINDUCTION if 'co-induction' in mode else
                     mode)
        assert type(self.mode) == S, f"Unsupported mode: {mode}"
        self.annotations = annotations.annotations if annotations else {}
        self.rules = rules
        self.clarks = {}  # {SymbolDeclaration: Transformed Rule}
        self.canonicals = {}
        self.instantiables = {}
        self.def_vars = {}  # {String: {String: Variable}}
        self.level_symbols = {}  # {SymbolDeclaration: Symbol}
        self.cache = {}  # {decl, str: Expression}
        self.inst_def_level = 0

    def __str__(self):
        return "Definition " +str(self.id)+" of " + ",".join([k.name for k in self.canonicals.keys()])

    def __repr__(self):
        out = []
        for rule in self.clarks.values():
            out.append(repr(rule))
        return NEWL.join(out)

    def __eq__(self, another):
        return self.id == another.id

    def __hash__(self):
        return hash(self.id)

    def instantiate_definition(self, decl, new_args, theory):
        rule = self.clarks.get(decl, None)
        if rule:
            key = str(new_args)
            if (decl, key) in self.cache:
                return self.cache[decl, key]

            if self.inst_def_level + 1 > CO_CONSTR_RECURSION_DEPTH:
                return None
            self.inst_def_level += 1
            self.cache[decl, key] = None

            out = rule.instantiate_definition(new_args, theory)

            self.cache[decl, key] = out
            self.inst_def_level -= 1
            return out

    def set_level_symbols(self, voc):
        """Calculates which symbols in the definition are recursively defined,
           creates a corresponding level mapping symbol,
           and stores these in self.level_symbols.
        """
        dependencies = set()
        for r in self.rules:
            symbs = {}
            r.body.collect_symbols(symbs)
            for s in symbs.values():
                dependencies.add((r.definiendum.symbol.decl, s))

        while True:
            new_relations = set((x, w) for x, y in dependencies
                                for q, w in dependencies if q == y)
            closure_until_now = dependencies | new_relations
            if len(closure_until_now) == len(dependencies):
                break
            dependencies = closure_until_now

        symbs = {s for (s, ss) in dependencies if s == ss}
        for r in self.rules:
            key = r.definiendum.symbol.decl
            if key not in symbs or key in self.level_symbols:
                continue

            real = TYPE(REAL)
            real.decl = voc.symbol_decls[REAL]
            symbdec = SymbolDeclaration.make(
                "_"+str(self.id)+"lvl_"+key.name,
                key.arity, key.sorts, real)
            self.level_symbols[key] = SYMBOL(symbdec.name)
            self.level_symbols[key].decl = symbdec

        for decl in self.level_symbols.keys():
            self.check(decl.out.name == BOOL,
                       f"Inductively defined functions are not supported yet: "
                       f"{decl.name}.")

        if len(self.level_symbols) > 0:  # check for nested recursive symbols
            nested = set()
            for r in self.rules:
                r.body.collect_nested_symbols(nested, False)
            for decl in self.level_symbols.keys():
                self.check(decl not in nested,
                           f"Inductively defined nested symbols are not supported yet: "
                           f"{decl.name}.")

class Rule(ASTNode):
    def __init__(self, **kwargs):
        self.annotations = kwargs.pop('annotations')
        self.quantees = kwargs.pop('quantees')
        self.definiendum = kwargs.pop('definiendum')
        self.out = kwargs.pop('out')
        self.body = kwargs.pop('body')
        self.has_finite_domain = None  # Bool
        self.block = None  # theory where it occurs

        self.annotations = self.annotations.annotations if self.annotations else {}

        if self.out is not None:
            self.definiendum.sub_exprs.append(self.out)
        if self.body is None:
            self.body = TRUE

    def __repr__(self):
        return (f"∀ {','.join(str(q) for q in self.quantees)}: "
                f"{self.definiendum} "
                f"{(' = ' + str(self.out)) if self.out else ''}"
                f"← {str(self.body)}")

    def instantiate_definition(self, new_args, theory):
        """Create an instance of the definition for new_args, and interpret it for theory.

        Args:
            new_args ([Expression]): tuple of arguments to be applied to the defined symbol
            theory (Theory): the context for the interpretation

        Returns:
            Expression: a boolean expression
        """

        out = deepcopy(self.body)  # in case there are no arguments
        instance = AppliedSymbol.make(self.definiendum.symbol, new_args)
        instance.in_head = True
        if self.definiendum.decl.type == BOOL:  # a predicate
            self.check(len(self.definiendum.sub_exprs) == len(new_args),
                       "Internal error")
            out = out.instantiate(self.definiendum.sub_exprs, new_args, theory)
            out = EQUIV([instance, out])
        else:
            self.check(len(self.definiendum.sub_exprs) == len(new_args)+1 ,
                       "Internal error")
            out = out.instantiate(self.definiendum.sub_exprs,
                                  new_args+[instance], theory)
        out.block = self.block
        out = out.interpret(theory)
        return out


# Expressions : see Expression.py

################################ Structure  ###############################

class Structure(ASTNode):
    """
    The class of AST nodes representing an structure block.
    """
    def __init__(self, **kwargs):
        """
        The textx parser creates the Structure object. All information used in
        this method directly comes from text.
        """
        self.name = kwargs.pop('name')
        self.vocab_name = kwargs.pop('vocab_name')
        self.interpretations = self.dedup_nodes(kwargs, 'interpretations')

        self.name = 'S' if not self.name else self.name
        self.vocab_name = 'V' if not self.vocab_name else self.vocab_name

        self.voc = None
        self.declarations = {}
        self.assignments = Assignments()

    def __str__(self):
        return self.name


class SymbolInterpretation(ASTNode):
    """
    AST node representing `<symbol> := { <identifiers*> } else <default>.`

    Attributes:
        name (string): name of the symbol being enumerated.

        symbol (Symbol): symbol being enumerated

        enumeration ([Enumeration]): enumeration.

        default (Expression): default value (for function enumeration).

        is_type_enumeration (Bool): True if the enumeration is for a type symbol.

    """
    def __init__(self, **kwargs):
        self.name = kwargs.pop('name').name
        self.sign = kwargs.pop('sign')
        self.enumeration = kwargs.pop('enumeration')
        self.default = kwargs.pop('default')

        if not self.enumeration:
            self.enumeration = Enumeration(tuples=[])

        self.sign = ('⊇' if self.sign == '>>' else
                     '≜' if self.sign == ':=' else self.sign)
        self.check(self.sign == '≜' or
                   (type(self.enumeration) == FunctionEnum and self.default is None),
                   "'⊇' can only be used with a functional enumeration ('→') without else clause")

        self.symbol = None
        self.is_type_enumeration = None

    def __repr__(self):
        return f"{self.name} {self.sign} {self.enumeration}"

    def interpret_application(self, rank, applied, args, tuples=None):
        """returns an expression equivalent to `self.symbol` applied to `args`,
        simplified by the interpretation of `self.symbol`.

        This is a recursive function.

        Example: assume `f>>{(1,2)->A, (1, 3)->B, (2,1)->C}` and `args=[g(1),2)].
        The returned expression is:
        ```
        if g(1) = 1 then A
        else if g(1)=2 then f(g(1),2)
        else f(g(1),2)
        ```

        Args:
            rank (Int): iteration number (from 0)

            applied (AppliedSymbol): template to create new AppliedSymbol
                (ex: `g(1),a()`, before interpretation)

            args (List(Expression)): interpreted arguments applied to the symbol (ex: `g(1),2`)

            tuples (OrderedSet[TupleIDP], optional): relevant tuples for this iteration.
                Initialized with `[[1,2,A], [1,3,B], [2,1,C]]`

        Returns:
            Expression: Grounded interpretation of self.symbol applied to args
        """
        if tuples == None:  # first call
            tuples = self.enumeration.sorted_tuples
            key = ",".join(a.code for a in args)
            if key in self.enumeration.lookup:
                return self.enumeration.lookup[key]
        # in case of partial interpretation
        return applied._change(sub_exprs=args)
    """
        if rank == self.symbol.decl.arity:  # valid tuple -> return a value
            if not type(self.enumeration) == FunctionEnum:
                return TRUE if tuples else self.default
            else:
                self.check(len(tuples) <= 1,
                           f"Duplicate values in structure "
                           f"for {str(self.name)}{str(tuples[0])}")
                return (self.default if not tuples else  # enumeration of constant
                        tuples[0].args[rank])
        else:  # constructs If-then-else recursively
            out = (self.default if self.default is not None else
                   applied._change(sub_exprs=args))
            groups = groupby(tuples, key=lambda t: str(t.args[rank]))

            if args[rank].value is not None:
                for val, tuples2 in groups:  # try to resolve
                    if str(args[rank]) == val:
                        out = self.interpret_application(rank+1,
                                        applied, args, list(tuples2))
            else:
                for val, tuples2 in groups:
                    tuples = list(tuples2)
                    out = IF(
                        EQUALS([args[rank], tuples[0].args[rank]]),
                        self.interpret_application(rank+1,
                                                   applied, args, tuples),
                        out)
            return out
    """


class Enumeration(ASTNode):
    """Represents an enumeration of tuples of expressions.
    Used for predicates, or types without n-ary constructors.

    Attributes:
        tuples (OrderedSet[TupleIDP]): OrderedSet of TupleIDP of Expression

        sorted_tuples: a sorted list of tuples

        lookup: dictionary from arguments to values

        constructors (List[Constructor], optional): List of Constructor
    """
    def __init__(self, **kwargs):
        self.tuples = kwargs.pop('tuples')
        self.sorted_tuples = sorted(self.tuples, key=lambda t: t.code)  # do not change dropdown order
        self.tuples = OrderedSet(self.tuples)

        self.lookup = {}
        if all(len(c.args) == 1 and type(c.args[0]) == UnappliedSymbol
               for c in self.tuples):
            self.constructors = [CONSTRUCTOR(c.args[0].name)
                                 for c in self.tuples]
        else:
            self.constructors = None

    def __repr__(self):
        return (f'{{{", ".join([repr(t) for t in self.tuples])}}}' if self.tuples else
                f'{{{", ".join([repr(t) for t in self.constructors])}}}')

    def contains(self, args, function, arity=None, rank=0, tuples=None,
                 interpretations: Dict[str, "SymbolInterpretation"]=None,
                 extensions: Dict[str, Extension]=None
                 ) -> Expression:
        """ returns an Expression that says whether Tuple args is in the enumeration """

        if arity is None:
            arity = len(args)
        if rank == arity:  # valid tuple
            return TRUE
        if tuples is None:
            tuples = self.sorted_tuples

        # constructs If-then-else recursively
        groups = groupby(tuples, key=lambda t: str(t.args[rank]))
        if args[rank].value is not None:
            for val, tuples2 in groups:  # try to resolve
                if str(args[rank]) == val:
                    return self.contains(args, function, arity, rank+1, list(tuples2),
                                interpretations=interpretations, extensions=extensions)
            return FALSE
        else:
            if rank + 1 == arity:  # use OR
                out = [ EQUALS([args[rank], t.args[rank]])
                        for t in tuples]
                out = OR(out)
                out.enumerated = ', '.join(str(c) for c in tuples)
                return out
            out = FALSE
            for val, tuples2 in groups:
                tuples = list(tuples2)
                out = IF(EQUALS([args[rank], tuples[0].args[rank]]),
                    self.contains(args, function, arity, rank+1, tuples,
                            interpretations=interpretations, extensions=extensions),
                    out)
            return out

    def extensionE(self,
                   interpretations: Dict[str, "SymbolInterpretation"]=None,
                   extensions: Dict[str, Extension]=None
                  ) -> Extension:
        """computes the extension of an enumeration, i.e., a set of tuples and a filter

        Args:
            interpretations (Dict[str, &quot;SymbolInterpretation&quot;], optional): _description_. Defaults to None.
            extensions (Dict[str, Extension], optional): _description_. Defaults to None.

        Returns:
            Extension: _description_
        """
        ranges = [c.range for c in self.constructors]
        return ([[t] for r in ranges for t in r], None)


class FunctionEnum(Enumeration):
    def extensionE(self,
                   interpretations: Dict[str, "SymbolInterpretation"]=None,
                   extensions: Dict[str, Extension]=None
                  ) -> Extension:
        self.check(False,
                   f"Can't use function enumeration for type declaration or quantification")


class CSVEnumeration(Enumeration):
    pass


class ConstructedFrom(Enumeration):
    """Represents a 'constructed from' enumeration of constructors

    Attributes:
        tuples (OrderedSet[TupleIDP]): OrderedSet of tuples of Expression

        constructors (List[Constructor]): List of Constructor

        accessors (Dict[str, Int]): index of the accessor in the constructors
    """
    def __init__(self, **kwargs):
        self.constructed = kwargs.pop('constructed')
        self.constructors = kwargs.pop('constructors')
        self.tuples = None
        self.accessors = dict()

    def contains(self, args, function, arity=None, rank=0, tuples=None,
                 interpretations: Dict[str, "SymbolInterpretation"]=None,
                 extensions: Dict[str, Extension]=None
                 ) -> Expression:
        """returns True if args belong to the type enumeration"""
        # args must satisfy the tester of one of the constructors
        assert len(args) == 1, f"Incorrect arity in {self.parent.name}{args}"
        if type(args[0].decl) == Constructor:  # try to simplify it
            self.check(self.parent.name == args[0].decl.type,
                       f"Incorrect type of {args[0]} for {self.parent.name}")
            self.check(len(args[0].sub_exprs) == len(args[0].decl.sorts),
                       f"Incorrect arity")
            return AND([t.decl.out.has_element(e, interpretations, extensions)
                        for e,t in zip(args[0].sub_exprs, args[0].decl.sorts)])
        out = [AppliedSymbol.construct(constructor.tester, args)
                for constructor in self.constructors]
        return OR(out)

    def extensionE(self,
                   interpretations: Dict[str, "SymbolInterpretation"]=None,
                   extensions: Dict[str, Extension]=None
                  ) -> Extension:
        def filter(args):
            if type(args[0]) != Variable and type(args[0].decl) == Constructor:  # try to simplify it
                self.check(self.parent.name == args[0].decl.type,
                        f"Incorrect type of {args[0]} for {self.parent.name}")
                self.check(len(args[0].sub_exprs) == len(args[0].decl.sorts),
                        f"Incorrect arity")
                return AND([t.decl.out.has_element(e, interpretations, extensions)
                            for e,t in zip(args[0].sub_exprs, args[0].decl.sorts)])
            out = [AppliedSymbol.construct(constructor.tester, args)
                    for constructor in self.constructors]
            return OR(out)  # return of filter()
        return (([t.args for t in self.tuples], None) if self.tuples else
                (None, filter))


class TupleIDP(ASTNode):
    def __init__(self, **kwargs):
        self.args = kwargs.pop('args')
        self.code = intern(",".join([str(a) for a in self.args]))

    def __str__(self):
        return self.code

    def __repr__(self):
        return f"({self.code})" if 1 < len(self.args) else self.code


class FunctionTuple(TupleIDP):
    def __init__(self, **kwargs):
        self.args = kwargs.pop('args')
        if not isinstance(self.args, list):
            self.args = [self.args]
        self.value = kwargs.pop('value')
        self.args.append(self.value)
        self.code = intern(",".join([str(a) for a in self.args]))


class CSVTuple(TupleIDP):
    pass


class Ranges(Enumeration):
    def __init__(self, **kwargs):
        self.elements = kwargs.pop('elements')

        tuples = []
        self.type = None
        if self.elements:
            self.type = self.elements[0].fromI.type
            for x in self.elements:
                if x.fromI.type != self.type:
                    if self.type in [INT, REAL] and x.fromI.type in [INT, REAL]:
                        self.type = REAL  # convert to REAL
                        tuples = [TupleIDP(args=[n.args[0].real()])
                                  for n in tuples]
                    else:
                        self.check(False,
                            f"incorrect value {x.fromI} for {self.type}")

                if x.toI is None:
                    tuples.append(TupleIDP(args=[x.fromI]))
                elif self.type == INT and x.fromI.type == INT and x.toI.type == INT:
                    for i in range(x.fromI.py_value, x.toI.py_value + 1):
                        tuples.append(TupleIDP(args=[Number(number=str(i))]))
                elif self.type == REAL and x.fromI.type == INT and x.toI.type == INT:
                    for i in range(x.fromI.py_value, x.toI.py_value + 1):
                        tuples.append(TupleIDP(args=[Number(number=str(float(i)))]))
                elif self.type == REAL:
                    self.check(False, f"Can't have a range over real: {x.fromI}..{x.toI}")
                elif self.type == DATE and x.fromI.type == DATE and x.toI.type == DATE:
                    for i in range(x.fromI.py_value, x.toI.py_value + 1):
                        d = Date(iso=f"#{date.fromordinal(i).isoformat()}")
                        tuples.append(TupleIDP(args=[d]))
                else:
                    self.check(False, f"Incorrect value {x.toI} for {self.type}")
        Enumeration.__init__(self, tuples=tuples)

    def contains(self, args, function, arity=None, rank=0, tuples=None,
                 interpretations: Dict[str, "SymbolInterpretation"]=None,
                 extensions: Dict[str, Extension]=None
                 ) -> Expression:
        var = args[0]
        if not self.elements:
            return TRUE
        if self.tuples and len(self.tuples) < MAX_QUANTIFIER_EXPANSION:
            es = [EQUALS([var, c.args[0]]) for c in self.tuples]
            e = OR(es)
            return e
        sub_exprs = []
        for x in self.elements:
            if x.toI is None:
                e = EQUALS([var, x.fromI])
            else:
                e = AComparison.make('≤', [x.fromI, var, x.toI])
            sub_exprs.append(e)
        return OR(sub_exprs)

    def extensionE(self,
                   interpretations: Dict[str, "SymbolInterpretation"]=None,
                   extensions: Dict[str, Extension]=None
                  ) -> Extension:
        if not self.elements:
            return(None, None)
        if self.tuples is not None: # and len(self.tuples) < MAX_QUANTIFIER_EXPANSION:
            return ([t.args for t in self.tuples], None)
        def filter(args):
            sub_exprs = []
            for x in self.elements:
                if x.toI is None:
                    e = EQUALS([args[0], x.fromI])
                else:
                    e = AComparison.make('≤', [x.fromI, args[0], x.toI])
                sub_exprs.append(e)
            return OR(sub_exprs)
        return(None, filter)


class RangeElement(ASTNode):
    def __init__(self, **kwargs):
        self.fromI = kwargs.pop('fromI')
        self.toI = kwargs.pop('toI')


class IntRange(Ranges):
    def __init__(self):
        Ranges.__init__(self, elements=[])
        self.type = INT
        self.tuples = None

    def extensionE(self,
                   interpretations: Dict[str, "SymbolInterpretation"]=None,
                   extensions: Dict[str, Extension]=None
                  ) -> Extension:
        return (None, None)


class RealRange(Ranges):
    def __init__(self):
        Ranges.__init__(self, elements=[])
        self.type = REAL
        self.tuples = None

    def extensionE(self,
                   interpretations: Dict[str, "SymbolInterpretation"]=None,
                   extensions: Dict[str, Extension]=None
                  ) -> Extension:
        return (None, None)


class DateRange(Ranges):
    def __init__(self):
        Ranges.__init__(self, elements=[])
        self.type = DATE
        self.tuples = None

    def extensionE(self,
                   interpretations: Dict[str, "SymbolInterpretation"]=None,
                   extensions: Dict[str, Extension]=None
                  ) -> Extension:
        return (None, None)


################################ Display  ###############################

class Display(ASTNode):
    def __init__(self, **kwargs):
        self.constraints = kwargs.pop('constraints')
        self.interpretations = self.dedup_nodes(kwargs, 'interpretations')
        self.moveSymbols = False
        self.optionalPropagation = False
        self.manualPropagation = False
        self.optionalRelevance = False
        self.manualRelevance = False
        self.name = "display"

    def run(self, idp):
        """apply the display block to the idp theory"""

        def base_symbols(name, concepts):
            """Verify that concepts is a list of concepts.  Returns the list of symbols"""
            symbols = []
            # All concepts should be concepts, except for the first
            # argument of 'unit' and 'heading'.
            for i, symbol in enumerate(concepts):
                if name in ['unit', 'heading'] and i == 0:
                    continue
                self.check(symbol.name.startswith('`'),
                    f"arg '{symbol.name}' of {name}'"
                    f" must begin with a tick '`'")
                self.check(symbol.name[1:] in self.voc.symbol_decls,
                    f"argument '{symbol.name}' of '{name}'"
                    f" must be a concept")
                symbols.append(self.voc.symbol_decls[symbol.name[1:]])
            return symbols

        for k, interpretation in self.interpretations.items():
            symbols = base_symbols(interpretation.name,
                [t.args[0] for t in interpretation.enumeration.tuples])
            if interpretation.name == EXPAND:
                for symbol in symbols:
                    self.voc.symbol_decls[symbol.name].view = ViewType.EXPANDED
            elif interpretation.name == GOAL_SYMBOL:
                idp.theory.interpretations[k] = interpretation
            else:
                raise IDPZ3Error(f"Unknown enumeration in display: {interpretation}")
        for constraint in self.constraints:
            if type(constraint) == AppliedSymbol:
                self.check(type(constraint.symbol.sub_exprs[0]) == Symbol,
                           f"Invalid syntax: {constraint}")
                name = constraint.symbol.sub_exprs[0].name
                symbols = base_symbols(name, constraint.sub_exprs)

                if name == 'hide':  # e.g. hide(Length, Angle)
                    for symbol in symbols:
                        self.voc.symbol_decls[symbol.name].view = ViewType.HIDDEN
                elif name in [GOAL_SYMBOL, EXPAND]:  # e.g. goal_symbol(`tax_amount`)
                    self.check(False, f"Please use an enumeration for {name}")
                elif name == 'unit':  # e.g. unit('m', `length):
                    for symbol in symbols:
                        symbol.unit = str(constraint.sub_exprs[0])
                elif name == 'heading':
                    # e.g. heading('Shape', `type).
                    for symbol in symbols:
                        symbol.heading = str(constraint.sub_exprs[0])
                elif name == 'noOptimization':  # e.g., noOptimization(`temp)
                    for symbol in symbols:
                        symbol.optimizable = False
                elif name == "moveSymbols":
                    self.moveSymbols = True
                elif name == "optionalPropagation":
                    self.optionalPropagation = True
                elif name == "manualPropagation":
                    self.manualPropagation = True
                elif name == "optionalRelevance":
                    self.optionalRelevance = True
                elif name == "manualRelevance":
                    self.manualRelevance = True
                else:
                    raise IDPZ3Error(f"Unknown display axiom:"
                                     f" {constraint}")
            elif type(constraint) == AComparison:  # e.g. view = normal
                self.check(constraint.is_assignment(), "Internal error")
                self.check(type(constraint.sub_exprs[0].symbol.sub_exprs[0]) == Symbol,
                           f"Invalid syntax: {constraint}")
                if constraint.sub_exprs[0].symbol.sub_exprs[0].name == 'view':
                    if constraint.sub_exprs[1].name == 'expanded':
                        for s in self.voc.symbol_decls.values():
                            if type(s) == SymbolDeclaration and s.view == ViewType.NORMAL:
                                s.view = ViewType.EXPANDED  # don't change hidden symbols
                    else:
                        self.check(constraint.sub_exprs[1].name == 'normal',
                                   f"Unknown display axiom: {constraint}")
            else:
                raise IDPZ3Error(f"Unknown display axiom: {constraint}")


################################ Main  ##################################

class Procedure(ASTNode):
    def __init__(self, **kwargs):
        self.name = kwargs.pop('name')
        self.args = kwargs.pop('args')
        self.pystatements = kwargs.pop('pystatements')

    def __str__(self):
        return f"{NEWL.join(str(s) for s in self.pystatements)}"


class Call1(ASTNode):
    def __init__(self, **kwargs):
        self.name = kwargs.pop('name')
        self.par = kwargs.pop('par') if 'par' in kwargs else None
        self.args = kwargs.pop('args')
        self.kwargs = kwargs.pop('kwargs')
        self.post = kwargs.pop('post')

    def __str__(self):
        kwargs = ("" if len(self.kwargs)==0 else
                  f"{',' if self.args else ''}{','.join(str(a) for a in self.kwargs)}")
        args = ("" if not self.par else
                f"({','.join(str(a) for a in self.args)}{kwargs})")
        return ( f"{self.name}{args}"
                 f"{'' if self.post is None else '.'+str(self.post)}")


class String(ASTNode):
    def __init__(self, **kwargs):
        self.literal = kwargs.pop('literal')

    def __str__(self):
        return f'{self.literal}'


class PyList(ASTNode):
    def __init__(self, **kwargs):
        self.elements = kwargs.pop('elements')

    def __str__(self):
        return f"[{','.join(str(e) for e in self.elements)}]"


class PyAssignment(ASTNode):
    def __init__(self, **kwargs):
        self.var = kwargs.pop('var')
        self.val = kwargs.pop('val')

    def __str__(self):
        return f'{self.var} = {self.val}'


class MultiAssignment(ASTNode):
    def __init__(self, **kwargs):
        self.vars = kwargs.pop('vars')
        self.val = kwargs.pop('val')

    def __str__(self):
        return f'{",".join(self.vars)} = {self.val}'


########################################################################

Block = Union[Vocabulary, TheoryBlock, Structure, Display]

dslFile = path.join(path.dirname(__file__), 'Idp.tx')

idpparser = metamodel_from_file(dslFile, memoization=True,
                                classes=[IDP, Annotations,

                                         Vocabulary, Import, VarDeclaration,
                                         TypeDeclaration, Accessor, Type,
                                         SymbolDeclaration, Symbol,
                                         SymbolExpr,

                                         TheoryBlock, Definition, Rule, AIfExpr,
                                         AQuantification, Quantee, ARImplication,
                                         AEquivalence, AImplication,
                                         ADisjunction, AConjunction,
                                         AComparison, ASumMinus, AMultDiv,
                                         APower, AUnary, AAggregate,
                                         AppliedSymbol, UnappliedSymbol,
                                         Number, Brackets, Date, Variable,

                                         Structure, SymbolInterpretation,
                                         Enumeration, FunctionEnum, CSVEnumeration,
                                         TupleIDP, FunctionTuple, CSVTuple,
                                         ConstructedFrom, Constructor, Ranges,
                                         RangeElement, Display,

                                         Procedure, Call1, String,
                                         PyList, PyAssignment, MultiAssignment])
