"""Core propositional default logic engine (independent from the GUI).

Formula syntax: atoms (p, P, P(x)), negation ~, conjunction &, disjunction |,
implication ->, equivalence <->, and parentheses. Predicates are treated as
atomic propositions; quantifiers and first-order unification are not implemented.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from itertools import product, combinations
import re

TOKEN_RE = re.compile(r"<->|->|[()&,|~]|[A-Za-z_][A-Za-z0-9_]*(?:\([^()]*\))?")

class FormulaError(ValueError):
    pass

@dataclass(frozen=True)
class Node:
    op: str
    left: 'Node | None' = None
    right: 'Node | None' = None
    atom: str | None = None

    
    def atoms(self) -> set[str]:
        if self.op == 'atom':
            if self.atom is None:
                raise ValueError("Atom node has no atom")
            return {self.atom}

        out: set[str] = set()

        if self.left is not None:
            out |= self.left.atoms()

        if self.right is not None:
            out |= self.right.atoms()

        return out



    def evaluate(self, env):
     if self.op == 'atom':
         return env[self.atom]

     if self.op == 'not':
         if self.left is None:
             raise ValueError("Negation node has no child")
         return not self.left.evaluate(env)

     if self.left is None or self.right is None:
        raise ValueError(f"Operator {self.op} requires two operands")

     a = self.left.evaluate(env)
     b = self.right.evaluate(env)

     return {
        'and': a and b,
        'or': a or b,
        'imp': (not a) or b,
        'iff': a == b
     }[self.op]

class Parser:
    def __init__(self, text):
        self.text = text.strip()
        self.tokens = TOKEN_RE.findall(self.text)
        if not self.tokens or ''.join(self.tokens).replace(' ', '') != re.sub(r'\s+', '', self.text):
            raise FormulaError(f"Formule invalide : {text}")
        self.i = 0
    def peek(self): return self.tokens[self.i] if self.i < len(self.tokens) else None
    def take(self, token=None):
        t = self.peek()
        if t is None or (token is not None and t != token): raise FormulaError(f"Symbole attendu : {token or 'expression'}")
        self.i += 1; return t
    def parse(self):
        n = self.iff()
        if self.peek() is not None: raise FormulaError(f"Symbole inattendu : {self.peek()}")
        return n
    def iff(self):
        n = self.imp()
        while self.peek() == '<->': self.take(); n = Node('iff', n, self.imp())
        return n
    def imp(self):
        n = self.disj()
        if self.peek() == '->': self.take(); n = Node('imp', n, self.imp())
        return n
    def disj(self):
        n = self.conj()
        while self.peek() == '|': self.take(); n = Node('or', n, self.conj())
        return n
    def conj(self):
        n = self.unary()
        while self.peek() == '&': self.take(); n = Node('and', n, self.unary())
        return n
    def unary(self):
        if self.peek() == '~': self.take(); return Node('not', self.unary())
        if self.peek() == '(':
            self.take(); n = self.iff(); self.take(')'); return n
        t = self.take()
        if t in {'&','|','->','<->',')'}: raise FormulaError('Atome attendu')
        return Node('atom', atom=t)

def parse_formula(text): return Parser(text).parse()

def _models(formulas):
    nodes = [parse_formula(f) if isinstance(f, str) else f for f in formulas]
    atoms = sorted(set().union(*(n.atoms() for n in nodes))) if nodes else []
    for values in product([False, True], repeat=len(atoms)):
        env = dict(zip(atoms, values))
        if all(n.evaluate(env) for n in nodes): yield env

def consistent(formulas):
    return next(_models(formulas), None) is not None

def entails(premises, conclusion):
    nodes = [parse_formula(f) if isinstance(f, str) else f for f in premises]
    c = parse_formula(conclusion) if isinstance(conclusion, str) else conclusion
    atoms = sorted(set().union(*(n.atoms() for n in nodes), c.atoms()))
    for values in product([False, True], repeat=len(atoms)):
        env = dict(zip(atoms, values))
        if all(n.evaluate(env) for n in nodes) and not c.evaluate(env):
            return False
    return True

def equivalent_theories(a, b):
    atoms = sorted(set().union(*(parse_formula(x).atoms() for x in list(a)+list(b))))
    for vals in product([False, True], repeat=len(atoms)):
        env = dict(zip(atoms, vals))
        if all(parse_formula(x).evaluate(env) for x in a) != all(parse_formula(x).evaluate(env) for x in b): return False
    return True

@dataclass
class Default:
    prerequisite: str
    justifications: list[str]
    consequent: str
    def display(self): return f"{self.prerequisite} : {', '.join(self.justifications)} / {self.consequent}"
    def validate(self):
        parse_formula(self.prerequisite); parse_formula(self.consequent)
        if not self.justifications: raise FormulaError('Un défaut doit avoir au moins une justification.')
        for j in self.justifications: parse_formula(j)

@dataclass
class Theory:
    world: list[str]
    defaults: list[Default]
    def validate(self):
        for f in self.world: parse_formula(f)
        for d in self.defaults: d.validate()

class DefaultLogic:
    def __init__(self, theory: Theory):
        theory.validate(); self.theory = theory
    def generate_extensions(self, max_defaults=18):
        """Compute Reiter extensions by candidate enumeration and Gamma iteration.

        A candidate E is represented by W plus a subset of default consequents.
        Gamma(E) is built from Th(W), repeatedly adding consequents whose
        prerequisites follow at the current stage and whose justifications are
        consistent with the candidate E. The candidate is an extension exactly
        when Gamma(E) and E have the same classical models.
        """
        ds = self.theory.defaults
        if len(ds) > max_defaults:
            raise ValueError(f"{len(ds)} défauts : limite de sécurité {max_defaults} (2^n candidats).")
        results = []
        for mask in range(1 << len(ds)):
            selected = [i for i in range(len(ds)) if mask & (1 << i)]
            candidate = self.theory.world + [ds[i].consequent for i in selected]
            if not consistent(candidate):
                continue
            generated = list(self.theory.world)
            applied = []
            changed = True
            while changed:
                changed = False
                for i, d in enumerate(ds):
                    if i in applied:
                        continue
                    justifications_ok = all(consistent(candidate + [j]) for j in d.justifications)
                    if justifications_ok and entails(generated, d.prerequisite):
                        generated.append(d.consequent)
                        applied.append(i)
                        changed = True
            if equivalent_theories(candidate, generated):
                if not any(equivalent_theories(e['basis'], candidate) for e in results):
                    results.append({'selected': applied, 'basis': generated,
                                    'defaults': [ds[i].display() for i in applied]})
        return results
    def consequence(self, formula, extensions):
        parse_formula(formula)
        if not extensions: return {'skeptical': False, 'credulous': False, 'per_extension': []}
        checks = [entails(e['basis'], formula) for e in extensions]
        return {'skeptical': all(checks), 'credulous': any(checks), 'per_extension': checks}
    def diagnostics(self):
        warnings = []
        if not consistent(self.theory.world):
            warnings.append('Le monde W est incohérent : il ne possède pas de modèle classique.')
        for i, default in enumerate(self.theory.defaults, 1):
            # The assignment explicitly requires checking each justification on its own.
            # For example, the formula "x & ~x" has no classical model, so this
            # default can never be applicable.
            for justification in default.justifications:
                if not consistent([justification]):
                    warnings.append(
                        f"d{i} : la justification « {justification} » est incohérente ; "
                        "ce défaut ne sera jamais applicable."
                    )
            # Also report the separate case where individually consistent
            # justifications cannot all hold together.
            if len(default.justifications) > 1 and not consistent(default.justifications):
                warnings.append(
                    f"d{i} : les justifications sont conjointement incohérentes "
                    "(elles sont incompatibles entre elles)."
                )
        return warnings
