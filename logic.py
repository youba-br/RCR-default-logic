"""Core propositional default logic engine (independent from the GUI).

Moteur de la logique des défauts de Reiter (logique propositionnelle).
Ce module ne dépend d'aucune bibliothèque graphique : toute la logique est ici,
l'interface (app.py) se contente de l'appeler.

Formula syntax: atoms (p, P, P(x)), negation ~, conjunction &, disjunction |,
implication ->, equivalence <->, and parentheses. Predicates are treated as
atomic propositions; quantifiers and first-order unification are not implemented.

Organisation du fichier :
  1. Analyse syntaxique des formules (Node, Parser, parse_formula)
  2. Raisonnement classique par tables de vérité (consistent, entails, ...)
  3. Structures de la logique des défauts (Default, Theory)
  4. Algorithme des extensions, conséquences sceptique/crédule, diagnostics
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from itertools import product, combinations
import re

# Découpage d'une formule en jetons (tokens), dans cet ordre de priorité :
#   "<->" puis "->" (opérateurs longs d'abord), puis les symboles simples ( ) & , | ~
#   puis un atome : un identifiant éventuellement suivi d'arguments entre
#   parenthèses, ex. p, Oiseau, Vole(tweety), R(x, y).
# Les arguments entre parenthèses font partie de l'atome (pas de logique du 1er ordre).
TOKEN_RE = re.compile(r"<->|->|[()&,|~]|[A-Za-z_][A-Za-z0-9_]*(?:\([^()]*\))?")

class FormulaError(ValueError):
    """Erreur de syntaxe dans une formule ou un défaut (message affiché à l'utilisateur)."""
    pass

@dataclass(frozen=True)
class Node:
    """Noeud de l'arbre syntaxique d'une formule.

    op  : 'atom', 'not', 'and', 'or', 'imp' (implication) ou 'iff' (équivalence)
    left/right : sous-formules (right est None pour 'not' ; les deux sont None pour 'atom')
    atom : nom de l'atome, renseigné seulement si op == 'atom'
    """
    op: str
    left: 'Node | None' = None
    right: 'Node | None' = None
    atom: str | None = None


    def atoms(self) -> set[str]:
        """Retourne l'ensemble des atomes présents dans la formule (parcours récursif)."""
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
        """Évalue la formule pour une interprétation env : {atome: True/False}."""
        # Cas de base : la valeur de l'atome est donnée par l'interprétation
        if self.op == 'atom':
            return env[self.atom]

        # Négation : seul opérateur unaire, il n'utilise que le fils gauche
        if self.op == 'not':
            if self.left is None:
                raise ValueError("Negation node has no child")
            return not self.left.evaluate(env)

        # Opérateurs binaires : on évalue les deux fils puis on applique la table de vérité
        if self.left is None or self.right is None:
            raise ValueError(f"Operator {self.op} requires two operands")

        a = self.left.evaluate(env)
        b = self.right.evaluate(env)

        return {
            'and': a and b,
            'or': a or b,
            'imp': (not a) or b,   # a -> b  équivaut à  non a ou b
            'iff': a == b          # a <-> b : vrai si a et b ont la même valeur
        }[self.op]

class Parser:
    """Analyseur récursif descendant. Une méthode par niveau de priorité.

    Priorités (de la plus faible à la plus forte) :
        <->   <   ->   <   |   <   &   <   ~ et parenthèses
    '->' est associatif à droite (p -> q -> r = p -> (q -> r)),
    '<->', '|' et '&' sont associatifs à gauche.
    """
    def __init__(self, text):
        self.text = text.strip()
        self.tokens = TOKEN_RE.findall(self.text)
        # Vérification : les jetons reconnus, mis bout à bout, doivent redonner
        # exactement le texte (sans espaces). Sinon un caractère illégal a été ignoré
        # par la regex (ex. "p $ q") et la formule est refusée.
        if not self.tokens or ''.join(self.tokens).replace(' ', '') != re.sub(r'\s+', '', self.text):
            raise FormulaError(f"Formule invalide : {text}")
        self.i = 0  # position du jeton courant

    def peek(self):
        """Jeton courant sans le consommer (None en fin de formule)."""
        return self.tokens[self.i] if self.i < len(self.tokens) else None

    def take(self, token=None):
        """Consomme et retourne le jeton courant ; erreur s'il manque ou diffère de `token`."""
        t = self.peek()
        if t is None or (token is not None and t != token): raise FormulaError(f"Symbole attendu : {token or 'expression'}")
        self.i += 1; return t

    def parse(self):
        """Point d'entrée : analyse toute la formule et refuse les jetons restants."""
        n = self.iff()
        if self.peek() is not None: raise FormulaError(f"Symbole inattendu : {self.peek()}")
        return n

    def iff(self):
        # niveau le plus faible : a <-> b <-> c (boucle = associativité gauche)
        n = self.imp()
        while self.peek() == '<->': self.take(); n = Node('iff', n, self.imp())
        return n

    def imp(self):
        # a -> b : l'appel récursif à self.imp() donne l'associativité à droite
        n = self.disj()
        if self.peek() == '->': self.take(); n = Node('imp', n, self.imp())
        return n

    def disj(self):
        # a | b | c
        n = self.conj()
        while self.peek() == '|': self.take(); n = Node('or', n, self.conj())
        return n

    def conj(self):
        # a & b & c
        n = self.unary()
        while self.peek() == '&': self.take(); n = Node('and', n, self.unary())
        return n

    def unary(self):
        # ~f (négation, répétable : ~~f), (f) entre parenthèses, ou un atome
        if self.peek() == '~': self.take(); return Node('not', self.unary())
        if self.peek() == '(':
            self.take(); n = self.iff(); self.take(')'); return n
        t = self.take()
        # un opérateur ou une parenthèse fermante ici signifie qu'un atome manque
        if t in {'&','|','->','<->',')'}: raise FormulaError('Atome attendu')
        return Node('atom', atom=t)

def parse_formula(text):
    """Transforme un texte en arbre Node (lève FormulaError si la syntaxe est incorrecte)."""
    return Parser(text).parse()

# ---------------------------------------------------------------------------
# Raisonnement classique par énumération des modèles (tables de vérité).
# Exact mais exponentiel en nombre d'atomes : suffisant pour des théories de TP.
# Les formules peuvent être passées en texte ou déjà analysées (Node).
# ---------------------------------------------------------------------------

def _models(formulas):
    """Générateur : produit chaque interprétation (dict) qui rend TOUTES les formules vraies."""
    nodes = [parse_formula(f) if isinstance(f, str) else f for f in formulas]
    atoms = sorted(set().union(*(n.atoms() for n in nodes))) if nodes else []
    # on essaie les 2^n affectations possibles de vrai/faux aux n atomes
    for values in product([False, True], repeat=len(atoms)):
        env = dict(zip(atoms, values))
        if all(n.evaluate(env) for n in nodes): yield env

def consistent(formulas):
    """Vrai si l'ensemble de formules possède au moins un modèle (cohérent)."""
    return next(_models(formulas), None) is not None

def entails(premises, conclusion):
    """Vrai si premises |= conclusion : aucun modèle des prémisses ne falsifie la conclusion."""
    nodes = [parse_formula(f) if isinstance(f, str) else f for f in premises]
    c = parse_formula(conclusion) if isinstance(conclusion, str) else conclusion
    atoms = sorted(set().union(*(n.atoms() for n in nodes), c.atoms()))
    for values in product([False, True], repeat=len(atoms)):
        env = dict(zip(atoms, values))
        # contre-exemple : prémisses vraies et conclusion fausse
        if all(n.evaluate(env) for n in nodes) and not c.evaluate(env):
            return False
    return True

def equivalent_theories(a, b):
    """Vrai si les ensembles a et b ont exactement les mêmes modèles (Th(a) = Th(b))."""
    atoms = sorted(set().union(*(parse_formula(x).atoms() for x in list(a)+list(b))))
    for vals in product([False, True], repeat=len(atoms)):
        env = dict(zip(atoms, vals))
        if all(parse_formula(x).evaluate(env) for x in a) != all(parse_formula(x).evaluate(env) for x in b): return False
    return True

# ---------------------------------------------------------------------------
# Structures de la logique des défauts
# ---------------------------------------------------------------------------

@dataclass
class Default:
    """Un défaut  prérequis : just1, just2, ... / conséquent  (formules stockées en texte)."""
    prerequisite: str
    justifications: list[str]
    consequent: str
    def display(self):
        """Forme affichable, au format de saisie : « α : β1, β2 / γ »."""
        return f"{self.prerequisite} : {', '.join(self.justifications)} / {self.consequent}"
    def validate(self):
        """Vérifie que chaque partie est une formule correcte et qu'il y a >= 1 justification."""
        parse_formula(self.prerequisite); parse_formula(self.consequent)
        if not self.justifications: raise FormulaError('Un défaut doit avoir au moins une justification.')
        for j in self.justifications: parse_formula(j)

@dataclass
class Theory:
    """Une théorie des défauts T = (W, D) : W = liste de formules, D = liste de Default."""
    world: list[str]
    defaults: list[Default]
    def validate(self):
        """Lève FormulaError si une formule de W ou un défaut de D est mal formé."""
        for f in self.world: parse_formula(f)
        for d in self.defaults: d.validate()

class DefaultLogic:
    """Calculs sur une théorie : extensions, conséquences, diagnostics."""
    def __init__(self, theory: Theory):
        theory.validate(); self.theory = theory  # refuse d'emblée une théorie mal formée

    def generate_extensions(self, max_defaults=18):
        """Compute Reiter extensions by candidate enumeration and Gamma iteration.

        A candidate E is represented by W plus a subset of default consequents.
        Gamma(E) is built from Th(W), repeatedly adding consequents whose
        prerequisites follow at the current stage and whose justifications are
        consistent with the candidate E. The candidate is an extension exactly
        when Gamma(E) and E have the same classical models.

        Retourne une liste de dictionnaires, un par extension :
          'basis'    : formules qui engendrent l'extension (E = Th(basis))
          'defaults' : défauts appliqués, sous forme de texte
          'selected' : indices (dans D) des défauts appliqués
        """
        ds = self.theory.defaults
        # garde-fou : on énumère 2^n sous-ensembles de défauts
        if len(ds) > max_defaults:
            raise ValueError(f"{len(ds)} défauts : limite de sécurité {max_defaults} (2^n candidats).")
        results = []
        # chaque entier `mask` code un sous-ensemble de défauts (bit i = défaut i choisi)
        for mask in range(1 << len(ds)):
            selected = [i for i in range(len(ds)) if mask & (1 << i)]
            # candidat E = W + conséquents des défauts supposés appliqués
            candidate = self.theory.world + [ds[i].consequent for i in selected]
            # un candidat incohérent est écarté (voir la limite sur W incohérent dans le rapport)
            if not consistent(candidate):
                continue
            # --- calcul de Gamma(E) : on part de W et on ajoute des conséquents ---
            generated = list(self.theory.world)
            applied = []        # indices des défauts appliqués dans Gamma(E)
            changed = True
            while changed:      # on itère jusqu'à ce qu'aucun défaut ne puisse plus s'appliquer
                changed = False
                for i, d in enumerate(ds):
                    if i in applied:
                        continue
                    # chaque justification doit être cohérente avec le CANDIDAT E
                    # (et non avec ce qui est déjà généré) : c'est la définition de Reiter
                    justifications_ok = all(consistent(candidate + [j]) for j in d.justifications)
                    # le prérequis doit être déduit de ce qui est généré jusqu'ici
                    if justifications_ok and entails(generated, d.prerequisite):
                        generated.append(d.consequent)
                        applied.append(i)
                        changed = True
            # E est une extension si E = Gamma(E), i.e. mêmes modèles
            if equivalent_theories(candidate, generated):
                # on évite les doublons (même extension obtenue par plusieurs sous-ensembles)
                if not any(equivalent_theories(e['basis'], candidate) for e in results):
                    results.append({'selected': applied, 'basis': generated,
                                    'defaults': [ds[i].display() for i in applied]})
        return results

    def consequence(self, formula, extensions):
        """Teste si `formula` est conséquence sceptique / crédule des extensions données.

        sceptique : vraie dans TOUTES les extensions ; crédule : vraie dans AU MOINS UNE.
        Sans extension, les deux réponses sont False (choix de convention).
        `per_extension` détaille le résultat pour chaque extension.
        """
        parse_formula(formula)  # lève FormulaError si la formule est invalide
        if not extensions: return {'skeptical': False, 'credulous': False, 'per_extension': []}
        checks = [entails(e['basis'], formula) for e in extensions]
        return {'skeptical': all(checks), 'credulous': any(checks), 'per_extension': checks}

    def diagnostics(self):
        """Retourne une liste d'avertissements (texte) sur la théorie, sans calculer les extensions."""
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
