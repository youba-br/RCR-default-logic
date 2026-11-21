"""Core propositional default-logic engine (independent from the GUI).

Moteur de la logique des défauts de Reiter (logique propositionnelle).

Formula syntax
--------------
Atoms: p, P, P(x), R(x, y)
Negation:       ~p
Conjunction:    p & q
Disjunction:    p | q
Implication:    p -> q
Equivalence:    p <-> q
Parentheses:    (p | q) & r

Predicates such as P(x) are treated as atomic propositions. Quantifiers and
first-order unification are not implemented.

The public names used by the rest of the project are preserved:
FormulaError, Node, Parser, parse_formula, _to_sympy, _conjunction,
consistent, entails, equivalent_theories, Default, Theory, and DefaultLogic.
"""

from __future__ import annotations

from dataclasses import dataclass
import re
from typing import Any

from sympy import And, Equivalent, Implies, Not, Or, Symbol, true
from sympy.logic.boolalg import Boolean
from sympy.logic.inference import satisfiable


# Long operators must be matched before their shorter prefixes.
# The optional (...) part belongs to the atom, so P(x, y) is one proposition.
TOKEN_RE = re.compile(
    r"<->|->|[()&|~]|[A-Za-z_][A-Za-z0-9_]*(?:\([^()]*\))?"
)


class FormulaError(ValueError):
    """Erreur de syntaxe dans une formule ou un défaut."""


@dataclass(frozen=True)
class Node:
    """A node in the propositional formula syntax tree.

    op is one of: 'atom', 'not', 'and', 'or', 'imp', or 'iff'.
    For an atom, only ``atom`` is populated. For a negation, ``left`` is the
    child. Binary operators use both ``left`` and ``right``.
    """

    op: str
    left: Node | None = None
    right: Node | None = None
    atom: str | None = None

    def atoms(self) -> set[str]:
        """Return every propositional atom occurring in this formula."""
        if self.op == "atom":
            return {self.atom} if self.atom is not None else set()

        found: set[str] = set()
        if self.left is not None:
            found.update(self.left.atoms())
        if self.right is not None:
            found.update(self.right.atoms())
        return found

    def to_sympy(self) -> Boolean:
        """Convert this syntax tree into a SymPy Boolean expression."""
        if self.op == "atom":
            if not self.atom:
                raise ValueError("Atom node has no atom")
            # Symbol also accepts predicate-like names such as P(tweety).
            return Symbol(self.atom)

        if self.op == "not":
            if self.left is None:
                raise ValueError("Negation node has no child")
            return Not(self.left.to_sympy())

        if self.left is None or self.right is None:
            raise ValueError(f"Operator {self.op!r} requires two operands")

        a = self.left.to_sympy()
        b = self.right.to_sympy()

        operators = {
            "and": lambda: And(a, b),
            "or": lambda: Or(a, b),
            "imp": lambda: Implies(a, b),
            "iff": lambda: Equivalent(a, b),
        }
        try:
            return operators[self.op]()
        except KeyError as exc:
            raise ValueError(f"Unknown formula operator: {self.op!r}") from exc


class Parser:
    """Recursive-descent parser with the project's original precedence rules.

    From lowest to highest precedence:
        <->, ->, |, &, ~ and parentheses.

    Implication is right-associative. Equivalence, disjunction, and
    conjunction are left-associative.
    """

    def __init__(self, text: str):
        if not isinstance(text, str):
            raise TypeError("Une formule doit être fournie sous forme de texte.")

        self.text = text.strip()
        self.tokens = self._tokenize(self.text)
        self.i = 0

    @staticmethod
    def _tokenize(text: str) -> list[str]:
        """Tokenize the whole input; never silently skip invalid characters."""
        tokens: list[str] = []
        position = 0

        while position < len(text):
            if text[position].isspace():
                position += 1
                continue

            match = TOKEN_RE.match(text, position)
            if match is None:
                bad_character = text[position]
                raise FormulaError(
                    f"Symbole invalide {bad_character!r} à la position {position}."
                )

            tokens.append(match.group(0))
            position = match.end()

        if not tokens:
            raise FormulaError("La formule est vide.")

        return tokens

    def peek(self) -> str | None:
        """Return the current token without consuming it."""
        return self.tokens[self.i] if self.i < len(self.tokens) else None

    def take(self, token: str | None = None) -> str:
        """Consume the current token, optionally checking its exact value."""
        current = self.peek()
        if current is None:
            expected = token or "expression"
            raise FormulaError(f"Symbole attendu : {expected}")
        if token is not None and current != token:
            raise FormulaError(f"Symbole attendu : {token}, trouvé : {current}")

        self.i += 1
        return current

    def parse(self) -> Node:
        """Parse a complete formula and reject any trailing token."""
        node = self.iff()
        remaining = self.peek()
        if remaining is not None:
            raise FormulaError(f"Symbole inattendu : {remaining}")
        return node

    def iff(self) -> Node:
        node = self.imp()
        while self.peek() == "<->":
            self.take("<->")
            node = Node("iff", node, self.imp())
        return node

    def imp(self) -> Node:
        node = self.disj()
        if self.peek() == "->":
            self.take("->")
            # Recursion on imp() makes implication right-associative.
            node = Node("imp", node, self.imp())
        return node

    def disj(self) -> Node:
        node = self.conj()
        while self.peek() == "|":
            self.take("|")
            node = Node("or", node, self.conj())
        return node

    def conj(self) -> Node:
        node = self.unary()
        while self.peek() == "&":
            self.take("&")
            node = Node("and", node, self.unary())
        return node

    def unary(self) -> Node:
        token = self.peek()

        if token == "~":
            self.take("~")
            return Node("not", self.unary())

        if token == "(":
            self.take("(")
            node = self.iff()
            self.take(")")
            return node

        if token is None or token in {"&", "|", "->", "<->", ")"}:
            raise FormulaError("Atome attendu")

        atom = self.take()
        return Node("atom", atom=atom)


def parse_formula(text: str) -> Node:
    """Convert text into a Node; raise FormulaError for invalid syntax."""
    return Parser(text).parse()


# ---------------------------------------------------------------------------
# Classical reasoning through SymPy.
# ---------------------------------------------------------------------------


def _to_sympy(formula: Any) -> Boolean:
    """Convert text or a Node to SymPy; accept a SymPy Boolean unchanged."""
    if isinstance(formula, Node):
        return formula.to_sympy()
    if isinstance(formula, str):
        return parse_formula(formula).to_sympy()
    if isinstance(formula, Boolean):
        return formula
    raise TypeError(
        "Une formule doit être une chaîne, un Node ou une expression booléenne SymPy."
    )


def _flatten_formulas(formulas: tuple[Any, ...]) -> list[Any]:
    """Expand lists/tuples/sets passed as a single collection of formulas."""
    flattened: list[Any] = []
    for formula in formulas:
        if isinstance(formula, (list, tuple, set)):
            flattened.extend(_flatten_formulas(tuple(formula)))
        else:
            flattened.append(formula)
    return flattened


def _conjunction(*formulas: Any) -> Boolean:
    """Return the conjunction of formulas; an empty collection means True.

    Both calling styles are supported:
        _conjunction("p", "q")
        _conjunction(["p", "q"])
    """
    items = _flatten_formulas(formulas)
    if not items:
        return true

    expressions = [_to_sympy(formula) for formula in items]
    return And(*expressions) if len(expressions) > 1 else expressions[0]


def consistent(*formulas: Any) -> bool:
    """Return True iff the supplied formulas are jointly satisfiable."""
    return satisfiable(_conjunction(*formulas)) is not False


def entails(*premises: Any, conclusion: Any = None) -> bool:
    """Return True iff the premises classically entail the conclusion.

    Supports both the positional form already used in the project:
        entails(["p", "p -> q"], "q")

    and the explicit keyword form:
        entails("p", "p -> q", conclusion="q")

    The test uses the standard refutation method: premises |= conclusion iff
    premises AND NOT conclusion is unsatisfiable.
    """
    premise_items = premises

    # Backward compatibility: the original project calls entails(premises, phi)
    # with the conclusion as the final positional argument.
    if conclusion is None:
        if len(premises) < 2:
            raise TypeError("entails() requires premises and a conclusion")
        premise_items = premises[:-1]
        conclusion = premises[-1]

    base = _conjunction(*premise_items)
    counterexample_formula = And(base, Not(_to_sympy(conclusion)))
    return satisfiable(counterexample_formula) is False


def _as_formula_arguments(value: Any) -> tuple[Any, ...]:
    """Treat a collection as several formulas and a single value as one."""
    if isinstance(value, (list, tuple, set)):
        return tuple(value)
    return (value,)


def equivalent_theories(a: Any, b: Any) -> bool:
    """Return True iff the two formula collections have the same models."""
    expr_a = _conjunction(*_as_formula_arguments(a))
    expr_b = _conjunction(*_as_formula_arguments(b))
    return satisfiable(Not(Equivalent(expr_a, expr_b))) is False


# ---------------------------------------------------------------------------
# Structures of Reiter default logic.
# ---------------------------------------------------------------------------


@dataclass
class Default:
    """A default: prerequisite : justification(s) / consequent."""

    prerequisite: str
    justifications: list[str]
    consequent: str

    def display(self) -> str:
        """Return the default in the project's input/display format."""
        return (
            f"{self.prerequisite} : {', '.join(self.justifications)} / "
            f"{self.consequent}"
        )

    def validate(self) -> None:
        """Validate the prerequisite, consequent, and all justifications."""
        parse_formula(self.prerequisite)
        parse_formula(self.consequent)

        if not self.justifications:
            raise FormulaError("Un défaut doit avoir au moins une justification.")

        for justification in self.justifications:
            parse_formula(justification)


@dataclass
class Theory:
    """A default theory T = (W, D), with facts W and defaults D."""

    world: list[str]
    defaults: list[Default]

    def validate(self) -> None:
        """Validate all world formulas and defaults."""
        for formula in self.world:
            parse_formula(formula)
        for default in self.defaults:
            default.validate()


class DefaultLogic:
    """Compute extensions, skeptical/credulous consequences, and diagnostics."""

    def __init__(self, theory: Theory):
        theory.validate()
        self.theory = theory

    def generate_extensions(self, max_defaults: int = 18) -> list[dict[str, Any]]:
        """Compute Reiter extensions by candidate enumeration and Gamma iteration.

        Each candidate E is represented by W plus a subset of default
        consequents. Gamma(E) starts from W and repeatedly adds consequents
        whose prerequisites follow from the generated formulas and whose
        justifications remain consistent with the candidate E.

        Each returned dictionary contains:
          'basis'    : formulas generating the extension (E = Th(basis))
          'defaults' : applied defaults, as display strings
          'selected' : indices of applied defaults in the original D list
        """
        defaults = self.theory.defaults
        if len(defaults) > max_defaults:
            raise ValueError(
                f"{len(defaults)} défauts : limite de sécurité {max_defaults} "
                "(2^n candidats)."
            )

        results: list[dict[str, Any]] = []

        # Enumerate all subsets of defaults (2^n candidates).
        for mask in range(1 << len(defaults)):
            selected = [
                i for i in range(len(defaults)) if mask & (1 << i)
            ]

            candidate = self.theory.world + [
                defaults[i].consequent for i in selected
            ]

            # Inconsistent candidates cannot be extensions.
            if not consistent(candidate):
                continue

            generated = list(self.theory.world)
            applied: list[int] = []
            changed = True

            while changed:
                changed = False
                for i, default in enumerate(defaults):
                    if i in applied:
                        continue

                    # Reiter's justifications are checked against candidate E.
                    justifications_ok = all(
                        consistent(candidate + [justification])
                        for justification in default.justifications
                    )

                    # The prerequisite must follow from what Gamma has generated.
                    if justifications_ok and entails(
                        generated, default.prerequisite
                    ):
                        generated.append(default.consequent)
                        applied.append(i)
                        changed = True

            # E is an extension iff E and Gamma(E) have the same models.
            if equivalent_theories(candidate, generated):
                # Avoid duplicate extensions generated by different subsets.
                if not any(
                    equivalent_theories(result["basis"], candidate)
                    for result in results
                ):
                    results.append(
                        {
                            "selected": applied,
                            "basis": generated,
                            "defaults": [
                                defaults[i].display() for i in applied
                            ],
                        }
                    )

        return results

    def consequence(
        self, formula: str, extensions: list[dict[str, Any]]
    ) -> dict[str, Any]:
        """Test skeptical and credulous consequence over given extensions.

        Skeptical: true in every extension.
        Credulous: true in at least one extension.
        With no extensions, both values are False by convention.
        """
        parse_formula(formula)
        if not extensions:
            return {
                "skeptical": False,
                "credulous": False,
                "per_extension": [],
            }

        checks = [entails(extension["basis"], formula) for extension in extensions]
        return {
            "skeptical": all(checks),
            "credulous": any(checks),
            "per_extension": checks,
        }

    def diagnostics(self) -> list[str]:
        """Return warnings about inconsistent facts or default justifications."""
        warnings: list[str] = []

        if not consistent(self.theory.world):
            warnings.append(
                "Le monde W est incohérent : il ne possède pas de modèle classique."
            )

        for i, default in enumerate(self.theory.defaults, 1):
            # Check each justification separately.
            for justification in default.justifications:
                if not consistent([justification]):
                    warnings.append(
                        f"d{i} : la justification « {justification} » est "
                        "incohérente ; ce défaut ne sera jamais applicable."
                    )

            # Also check whether the justifications are jointly consistent.
            if (
                len(default.justifications) > 1
                and not consistent(default.justifications)
            ):
                warnings.append(
                    f"d{i} : les justifications sont conjointement incohérentes "
                    "(elles sont incompatibles entre elles)."
                )

        return warnings
