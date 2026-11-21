"""PyQt6 graphical interface for the propositional default-logic mini-project.

Interface graphique (PyQt6) du mini-projet « logique des défauts ».
Règle du sujet : l'interface ne fait AUCUN calcul logique. Elle lit ce que
l'utilisateur saisit, appelle les fonctions de logic.py et affiche le résultat.

Organisation de la classe App :
  _build_ui            construction de la fenêtre (boutons, listes, zone de résultats)
  add_* / delete_*     saisie et suppression des formules de W et des défauts de D
  check_world,
  show_diagnostics,
  generate_extensions,
  test_consequence     appels au moteur (logic.py) et affichage des résultats
  save_* / open_file   sauvegarde et chargement JSON (W, D et extensions)
  import_txt_file      import d'une théorie depuis un fichier texte (option A du sujet)
  load_example         exemples prêts à l'emploi
"""
from __future__ import annotations

# NOTE : les deux imports suivants (email.header, logging.root) sont inutiles
# (ajoutés automatiquement par l'éditeur) ; ils peuvent être supprimés sans effet.
from email import header
import json
from logging import root
import sys
from pathlib import Path

from PyQt6.QtCore import Qt
from PyQt6.QtGui import QAction, QFont
from PyQt6.QtWidgets import (
    QApplication, QMainWindow, QMenu, QMenuBar, QWidget, QVBoxLayout, QHBoxLayout, QGridLayout,
    QLabel, QLineEdit, QPushButton, QListWidget, QListWidgetItem, QGroupBox,
    QTextEdit, QMessageBox, QFileDialog, QSplitter, QInputDialog, QStatusBar,
)

# Seules les fonctions du moteur sont utilisées ici : aucun calcul logique dans ce fichier
from logic import Theory, Default, DefaultLogic, FormulaError, parse_formula, consistent, entails

# Feuille de style Qt (apparence : couleurs, bordures arrondies, boutons)
APP_STYLE = """
QMainWindow, QWidget { background: #f4f6fa; color: #202938; font-family: 'Segoe UI', Arial; font-size: 10pt; }
QGroupBox { background: white; border: 1px solid #dce2eb; border-radius: 10px; margin-top: 12px; padding: 12px; font-weight: 600; }
QGroupBox::title { subcontrol-origin: margin; left: 12px; padding: 0 5px; color: #253b61; }
QLineEdit { background: #fbfcfe; border: 1px solid #cbd5e1; border-radius: 6px; padding: 8px; min-height: 18px; }
QLineEdit:focus { border: 1px solid #4776c7; }
QListWidget, QTextEdit { background: #fbfcfe; border: 1px solid #dce2eb; border-radius: 7px; padding: 6px; }
QPushButton { background: #e8edf5; border: 0; border-radius: 6px; padding: 8px 12px; font-weight: 600; }
QPushButton:hover { background: #d9e3f2; }
QPushButton#primary { background: #2859a6; color: white; }
QPushButton#primary:hover { background: #1e4788; }
QPushButton#danger { background: #fce8e8; color: #a52a2a; }
QLabel#subtitle { color: #65748b; }
QStatusBar { background: white; color: #65748b; }
"""

class App(QMainWindow):
    """Fenêtre principale : mémorise la théorie en cours de saisie et ses extensions."""


    def __init__(self):
        super().__init__()
        self.setWindowTitle("RCR | Logique des défauts")
        self.resize(1180, 820)
        self.setMinimumSize(960, 680)
        # État de l'application (ce que l'utilisateur a saisi / calculé)
        self.world: list[str] = []          # formules de W (texte)
        self.defaults: list[Default] = []   # défauts de D
        self.extensions: list[dict] = []    # extensions calculées (vide tant qu'on n'a pas cliqué)
        self.path: str | None = None        # fichier JSON courant (None = pas encore enregistré)
        self._build_ui()
        self._refresh_lists()
        self.status_bar = QStatusBar(self)
        self.setStatusBar(self.status_bar)
        self.status_bar.showMessage("Prêt — créez une théorie ou chargez un exemple.")

    def _build_ui(self):
        """Construit tous les widgets : en-tête, zones W et D, barre de calcul, résultats."""
        self.setStyleSheet(APP_STYLE)
        central = QWidget()
        root = QVBoxLayout(central)
        root.setContentsMargins(18, 14, 18, 14)
        root.setSpacing(12)

        # --- En-tête : titre + boutons Nouveau / Ouvrir / Importer TXT / Enregistrer / Exemples ---
        header = QHBoxLayout()
        titles = QVBoxLayout()
        title = QLabel("Logique des défauts")
        title.setFont(QFont("Segoe UI", 19, QFont.Weight.Bold))
        subtitle = QLabel("Représentation de connaissances et raisonnement · Mini-projet 1")
        subtitle.setObjectName("subtitle")
        titles.addWidget(title); titles.addWidget(subtitle)
        header.addLayout(titles); header.addStretch()

        for text, slot in [("Nouveau", self.new_theory), ("Ouvrir", self.open_file), ("Importer TXT", self.import_txt_file),
                   ("Enregistrer", self.save_file),
                   ("Exemples", self.load_example)]:

            b = QPushButton(text); b.clicked.connect(slot); header.addWidget(b)

        root.addLayout(header)


        # --- Partie centrale : à gauche le monde W, à droite les défauts D ---
        splitter = QSplitter(Qt.Orientation.Horizontal)
        world_box = QGroupBox("MONDE W — faits et formules")
        wl = QVBoxLayout(world_box)
        wl.addWidget(QLabel("Formule propositionnelle"))
        self.world_entry = QLineEdit(); self.world_entry.setPlaceholderText("Ex. : o   ou   p -> o   ou   p & ~q")
        self.world_entry.returnPressed.connect(self.add_world)   # touche Entrée = ajouter
        wl.addWidget(self.world_entry)
        buttons = QHBoxLayout()
        add_w = QPushButton("+ Ajouter formule"); add_w.setObjectName("primary"); add_w.clicked.connect(self.add_world)
        del_w = QPushButton("Supprimer sélection"); del_w.setObjectName("danger"); del_w.clicked.connect(lambda: self.delete_selected(self.world_list, self.world))
        buttons.addWidget(add_w); buttons.addWidget(del_w); wl.addLayout(buttons)
        self.world_list = QListWidget(); self.world_list.setSelectionMode(QListWidget.SelectionMode.ExtendedSelection); wl.addWidget(self.world_list, 1)
        check = QPushButton("Vérifier la cohérence de W"); check.clicked.connect(self.check_world); wl.addWidget(check)

        # Zone des défauts : trois champs (prérequis, justifications, conséquent)
        default_box = QGroupBox("DÉFAUTS D — règles par défaut")
        dl = QVBoxLayout(default_box)
        form = QGridLayout()
        form.addWidget(QLabel("Prérequis"), 0, 0); self.pre_entry = QLineEdit(); self.pre_entry.setPlaceholderText("Ex. : Oiseau(tweety)"); form.addWidget(self.pre_entry, 0, 1)
        form.addWidget(QLabel("Justifications"), 1, 0); self.just_entry = QLineEdit(); self.just_entry.setPlaceholderText("Séparées par des virgules : ~Anormal, EnBonneSante"); form.addWidget(self.just_entry, 1, 1)
        form.addWidget(QLabel("Conséquent"), 2, 0); self.cons_entry = QLineEdit(); self.cons_entry.setPlaceholderText("Ex. : Vole(tweety)"); form.addWidget(self.cons_entry, 2, 1)
        form.setColumnStretch(1, 1); dl.addLayout(form)
        db = QHBoxLayout()
        add_d = QPushButton("+ Ajouter défaut"); add_d.setObjectName("primary"); add_d.clicked.connect(self.add_default)
        del_d = QPushButton("Supprimer sélection"); del_d.setObjectName("danger"); del_d.clicked.connect(lambda: self.delete_selected(self.default_list, self.defaults))
        db.addWidget(add_d); db.addWidget(del_d); dl.addLayout(db)
        self.default_list = QListWidget(); self.default_list.setSelectionMode(QListWidget.SelectionMode.ExtendedSelection); dl.addWidget(self.default_list, 1)
        splitter.addWidget(world_box); splitter.addWidget(default_box); splitter.setSizes([520, 620])
        root.addWidget(splitter, 5)

        # --- Barre de calcul : générer les extensions, saisir φ, tester, diagnostic ---
        action_box = QGroupBox("CALCUL ET INTERROGATION")
        al = QHBoxLayout(action_box)
        generate = QPushButton("Générer les extensions"); generate.setObjectName("primary"); generate.clicked.connect(self.generate_extensions)
        al.addWidget(generate)
        al.addWidget(QLabel("Formule φ :"))
        self.query_entry = QLineEdit(); self.query_entry.setPlaceholderText("Ex. : Vole(tweety)"); self.query_entry.setMaximumWidth(260); al.addWidget(self.query_entry)
        ask = QPushButton("Tester sceptique / crédule"); ask.clicked.connect(self.test_consequence); al.addWidget(ask)
        diag = QPushButton("Diagnostic"); diag.clicked.connect(self.show_diagnostics); al.addWidget(diag)
        al.addStretch()
        root.addWidget(action_box)

        # --- Zone de résultats (lecture seule) : extensions, diagnostics, conséquences ---
        result_box = QGroupBox("RÉSULTATS")
        rl = QVBoxLayout(result_box)
        self.output = QTextEdit(); self.output.setReadOnly(True); self.output.setPlaceholderText("Les extensions, diagnostics et résultats des interrogations apparaîtront ici.")
        rl.addWidget(self.output)
        root.addWidget(result_box, 4)

        # Rappel de la syntaxe des formules, en bas de la fenêtre
        syntax = QLabel("Syntaxe : ~ négation   ·   & et   ·   | ou   ·   -> implication   ·   <-> équivalence   ·   parenthèses. P(x) est traité comme un atome.")
        syntax.setObjectName("subtitle"); syntax.setWordWrap(True); root.addWidget(syntax)
        self.setCentralWidget(central)


        # Menu « Fichier » (mêmes actions que les boutons de l'en-tête)
        self.menu_bar = QMenuBar(self)
        self.setMenuBar(self.menu_bar)

        file_menu = QMenu("Fichier", self)
        self.menu_bar.addMenu(file_menu)
        for label, slot in [("Nouvelle théorie", self.new_theory), ("Ouvrir…", self.open_file), ("Enregistrer", self.save_file), ("Enregistrer sous…", self.save_as)]:
            action = QAction(label, self); action.triggered.connect(slot); file_menu.addAction(action)

    # ------------------------------------------------------------------
    # Fonctions utilitaires
    # ------------------------------------------------------------------

    def _write(self, text: str):
        """Affiche `text` dans la zone de résultats (remplace le contenu précédent)."""
        self.output.setPlainText(text)

    def _invalidate_extensions(self):
        """Efface les extensions : elles sont périmées dès que W ou D change."""
        self.extensions = []

    def _refresh_lists(self):
        """Reconstruit les deux listes affichées (W numéroté 1., 2., … ; D numéroté d1, d2, …)."""
        self.world_list.clear()
        for i, formula in enumerate(self.world, 1): self.world_list.addItem(f"{i}.  {formula}")
        self.default_list.clear()
        for i, default in enumerate(self.defaults, 1): self.default_list.addItem(f"d{i} :  {default.display()}")

    def _error(self, title, error):
        """Boîte de message d'erreur avec le texte de l'exception."""
        QMessageBox.critical(self, title, str(error))

    # ------------------------------------------------------------------
    # Étape 1 : saisie des formules de W et des défauts de D
    # ------------------------------------------------------------------

    def add_world(self):
        """Ajoute la formule saisie à W après vérification de sa syntaxe."""
        formula = self.world_entry.text().strip()
        if not formula: return
        try: parse_formula(formula)
        except Exception as exc: self._error("Formule invalide", exc); return
        self.world.append(formula); self.world_entry.clear(); self._invalidate_extensions(); self._refresh_lists()
        self.status_bar.showMessage("Formule ajoutée au monde W.", 3000)

    def add_default(self):
        """Construit un défaut à partir des trois champs, le valide puis l'ajoute à D."""
        try:
            default = Default(
                self.pre_entry.text().strip(),
                # les justifications sont séparées par des virgules dans le champ de saisie
                [x.strip() for x in self.just_entry.text().split(",") if x.strip()],
                self.cons_entry.text().strip(),
            )
            default.validate()   # chaque partie doit être une formule correcte
        except Exception as exc:
            self._error("Défaut invalide", exc)
            return



        # Justifications individuellement incohérentes (ex. x & ~x) : le défaut est tout de
        # même ajouté, mais on avertit l'utilisateur car il ne sera jamais applicable.
        inconsistent_justifications = [
            justification
            for justification in default.justifications
            if not consistent([justification])
        ]

        self.defaults.append(default)
        for field in (self.pre_entry, self.just_entry, self.cons_entry):
            field.clear()
        self._invalidate_extensions()
        self._refresh_lists()
        self.status_bar.showMessage("Défaut ajouté à D.", 3000)

        if inconsistent_justifications:
            details = "\n".join(f"• {item}" for item in inconsistent_justifications)
            QMessageBox.warning(
                self,
                "Justification incohérente",
                "Le défaut a été ajouté, mais la ou les justifications suivantes "
                "sont incohérentes :\n\n"
                f"{details}\n\n"
                "Un défaut contenant une justification incohérente ne sera jamais applicable.",
            )

    def delete_selected(self, widget, collection):
        """Supprime de `collection` (W ou D) les éléments sélectionnés dans la liste `widget`."""
        # indices triés du plus grand au plus petit : supprimer de la fin évite de décaler les autres
        indexes = sorted({index.row() for index in widget.selectedIndexes()}, reverse=True)
        if not indexes: return
        for index in indexes: del collection[index]
        self._invalidate_extensions(); self._refresh_lists()

    def _theory(self):
        """Copie de la théorie courante (W, D), à passer au moteur."""
        return Theory(list(self.world), list(self.defaults))

    # ------------------------------------------------------------------
    # Appels au moteur : cohérence, diagnostic, extensions, conséquences
    # ------------------------------------------------------------------

    def check_world(self):
        """Bouton « Vérifier la cohérence de W »."""
        try: ok = consistent(self.world)
        except Exception as exc: self._error("Vérification impossible", exc); return
        self._write("W est cohérent : il possède au moins un modèle classique." if ok else "ATTENTION : W est incohérent (aucun modèle classique).")

    def show_diagnostics(self):
        """Bouton « Diagnostic » (fonctionnalité supplémentaire) : avertissements sur la théorie."""
        try: warnings = DefaultLogic(self._theory()).diagnostics()
        except Exception as exc: self._error("Diagnostic impossible", exc); return
        self._write("DIAGNOSTIC\n\n" + ("\n".join("• " + w for w in warnings) if warnings else "Aucun avertissement détecté. W et les justifications de chaque défaut sont cohérents."))

    def generate_extensions(self):
        """Étape 2 : calcule toutes les extensions (moteur) puis les affiche."""
        try:
            self.extensions = DefaultLogic(self._theory()).generate_extensions()
        except Exception as exc:
            self._error("Calcul impossible", exc)
            return

        if not self.extensions:
            self._write("Aucune extension trouvée.")
            return

        lines = [f"{len(self.extensions)} extension(s) trouvée(s)."]

        for i, extension in enumerate(self.extensions, 1):
            basis = extension["basis"]
            display_basis = list(basis)

            # Pour la lisibilité, on ajoute à l'affichage les littéraux (atome ou ~atome)
            # qui sont conséquences de la base mais n'y figurent pas explicitement.
            atoms = sorted(set().union(
                *(parse_formula(f).atoms() for f in basis)
            )) if basis else []

            for atom in atoms:
                if entails(basis, f"~{atom}"):
                    if f"~{atom}" not in display_basis:
                        display_basis.append(f"~{atom}")
                elif entails(basis, atom):
                    if atom not in display_basis:
                        display_basis.append(atom)

            lines += [
                "",
                f"E{i} = Th({{{'; '.join(display_basis)}}})",
                "Défauts appliqués : " +
                (" ; ".join(extension["defaults"])
                 if extension["defaults"] else "aucun")
            ]

        self._write("\n".join(lines))


    def test_consequence(self):
        """Étape 3 : teste si la formule φ saisie est conséquence sceptique / crédule."""
        formula = self.query_entry.text().strip()
        if not formula:
            QMessageBox.information(self, "Formule manquante", "Saisissez une formule φ à tester."); return
        # il faut avoir calculé (ou rechargé) les extensions avant d'interroger
        if not self.extensions:
            QMessageBox.information(self, "Extensions nécessaires", "Générez d’abord les extensions de la théorie."); return
        try: result = DefaultLogic(self._theory()).consequence(formula, self.extensions)
        except Exception as exc: self._error("Formule invalide", exc); return
        lines = [f"Formule testée : {formula}", "",
                 f"Conséquence sceptique : {'OUI' if result['skeptical'] else 'NON'}",
                 f"Conséquence crédule : {'OUI' if result['credulous'] else 'NON'}", "", "Détail par extension :"]
        lines += [f"E{i+1} : {'oui' if value else 'non'}" for i, value in enumerate(result['per_extension'])]
        self._write("\n".join(lines))

    # ------------------------------------------------------------------
    # Étape 4 : nouveau, sauvegarde et chargement (format JSON)
    # ------------------------------------------------------------------

    def new_theory(self):
        """Efface la théorie courante (après confirmation si elle n'est pas vide)."""
        if (self.world or self.defaults) and QMessageBox.question(self, "Nouvelle théorie", "Effacer la théorie actuelle ?") != QMessageBox.StandardButton.Yes: return
        self.world, self.defaults, self.extensions, self.path = [], [], [], None
        self._refresh_lists(); self._write("Nouvelle théorie créée.")

    def _serialize(self):
        """Dictionnaire à écrire en JSON : W, D et les extensions calculées."""
        return {
            "world": self.world,
            "defaults": [{"prerequisite": d.prerequisite, "justifications": d.justifications, "consequent": d.consequent} for d in self.defaults],
            "extensions": self.extensions,
        }

    def save_file(self):
        """« Enregistrer » : écrit dans le fichier courant, ou demande un nom s'il n'y en a pas."""
        if not self.path: return self.save_as()
        self._save_to(self.path)

    def save_as(self):
        """« Enregistrer sous… » : choix du fichier puis écriture."""
        path, _ = QFileDialog.getSaveFileName(self, "Enregistrer la théorie", "theorie.json", "Théorie JSON (*.json)")
        if path: self.path = path; self._save_to(path)

    def _save_to(self, path):
        """Écrit la théorie sérialisée dans `path` (JSON lisible, UTF-8)."""
        try:
            Path(path).write_text(json.dumps(self._serialize(), ensure_ascii=False, indent=2), encoding="utf-8")
            self.status_bar.showMessage(f"Théorie enregistrée : {path}", 5000)
            self._write(f"Théorie enregistrée avec succès :\n{path}")
        except Exception as exc: self._error("Enregistrement impossible", exc)

    def open_file(self):
        """Charge un fichier JSON : valide tout AVANT de remplacer la théorie courante."""
        path, _ = QFileDialog.getOpenFileName(self, "Ouvrir une théorie", "", "Théorie JSON (*.json);;Tous les fichiers (*)")
        if not path: return
        try:
            data = json.loads(Path(path).read_text(encoding="utf-8"))
            theory = Theory(data["world"], [Default(x["prerequisite"], x["justifications"], x["consequent"]) for x in data["defaults"]])
            theory.validate()
            restored_extensions = data.get("extensions", [])
            # Validate saved extension data before accepting it.
            for ext in restored_extensions:
                for formula in ext.get("basis", []): parse_formula(formula)
            # Tout est valide : on remplace seulement maintenant l'état de l'application.
            # En cas d'erreur plus haut, la théorie courante reste intacte.
            self.world, self.defaults = theory.world, theory.defaults
            self.extensions, self.path = restored_extensions, path
            self._refresh_lists()
            self._write(f"Théorie chargée : {path}\n{len(self.world)} formule(s), {len(self.defaults)} défaut(s), {len(self.extensions)} extension(s) sauvegardée(s).")
        except Exception as exc: self._error("Chargement impossible", exc)


    def import_txt_file(self):
        """Option A du sujet : importe W et D depuis un fichier texte.

        Format attendu :
            # Monde W
            une formule par ligne
            # Defauts D
            prérequis : just1, just2 / conséquent
        Les lignes commençant par '#' changent de section (« monde » ou « defaut »
        dans l'en-tête) ; les lignes vides sont ignorées.
        """
        path, _ = QFileDialog.getOpenFileName(
            self,
            "Importer une théorie depuis un fichier texte",
            "",
            "Fichiers texte (*.txt)"
        )

        if not path:
            return

        try:
            lines = Path(path).read_text(encoding="utf-8-sig").splitlines()

            world = []
            defaults = []

            section = None            # section courante : "world", "defaults" ou None
            found_world = False
            found_defaults = False

            for line_number, line in enumerate(lines, 1):
                line = line.strip()

                # Ignore empty lines
                if not line:
                    continue

                # Detect section headers and comments
                if line.startswith("#"):
                    header = line[1:].strip().lower()

                    if "monde" in header:
                        section = "world"
                        found_world = True

                    elif "defaut" in header:
                        section = "defaults"
                        found_defaults = True

                    continue

                # une formule avant tout en-tête de section est refusée
                if section is None:
                    raise ValueError(
                        f"Ligne {line_number}: "
                        "La formule doit être placée dans une section."
                    )

                try:
                    if section == "world":
                        # une ligne = une formule de W (syntaxe vérifiée)
                        parse_formula(line)
                        world.append(line)

                    elif section == "defaults":
                        # une ligne = un défaut « prérequis : just1, just2 / conséquent »
                        parts = line.split("/")

                        if len(parts) != 2:
                            raise ValueError(
                                "Format incorrect. Utilisez : "
                                "prérequis : justifications / conséquent"
                            )

                        left_part = parts[0].split(":")

                        if len(left_part) != 2:
                            raise ValueError(
                                "Il manque le symbole ':' dans le défaut."
                            )

                        prerequisite = left_part[0].strip()

                        justifications = [
                            x.strip()
                            for x in left_part[1].split(",")
                            if x.strip()
                        ]

                        consequent = parts[1].strip()

                        default = Default(
                            prerequisite,
                            justifications,
                            consequent
                        )

                        default.validate()
                        defaults.append(default)

                except Exception as exc:
                    # on indique le numéro de la ligne fautive dans le message
                    raise ValueError(
                        f"Erreur à la ligne {line_number}: {exc}"
                    ) from exc

            if not found_world or not found_defaults:
                raise ValueError(
                    "Le fichier doit contenir les deux sections : "
                    "# Monde W et # Defauts D."
                )

            # Validate the complete theory before modifying the GUI
            theory = Theory(world, defaults)
            theory.validate()

            # Check individually inconsistent justifications
            warnings = []

            for i, default in enumerate(defaults, 1):
                for justification in default.justifications:
                    if not consistent([justification]):
                        warnings.append(
                            f"d{i}: justification incohérente : "
                            f"{justification}"
                        )

            # Update the application
            self.world = theory.world
            self.defaults = theory.defaults
            self.extensions = []
            self.path = None

            self._refresh_lists()

            message = (
                f"Théorie importée avec succès !\n\n"
                f"Formules dans W : {len(world)}\n"
                f"Défauts dans D : {len(defaults)}"
            )

            if warnings:
                message += "\n\nAvertissements :\n"
                message += "\n".join(warnings)

            self._write(message)

            self.status_bar.showMessage(
                "Théorie importée depuis un fichier TXT.",
                5000
            )

            if warnings:
                QMessageBox.warning(
                    self,
                    "Importation avec avertissements",
                    message
                )

        except Exception as exc:
            self._error("Erreur d'importation", exc)


    def load_example(self):
        """Bouton « Exemples » : charge une théorie d'exemple choisie dans une liste."""
        examples = {
            "Exemple simple du sujet (o, p → o, p → ~v)": ( ["o", "p -> o", "p -> ~v"], [Default("o", ["v"], "v")] ),
            "Deux extensions possibles": (["p"], [Default("p", ["q"], "q"), Default("p", ["~q"], "~q")]),
            "Oiseau et anomalie": (["Oiseau(tweety)"], [Default("Oiseau(tweety)", ["~Anormal(tweety)"], "Vole(tweety)")]),
            "Défaut bloqué": (["oiseau", "~vole"], [Default("oiseau", ["vole"], "vole")]),
        }
        name, ok = QInputDialog.getItem(self, "Exemples", "Choisissez un exemple :", list(examples), 0, False)
        if not ok: return
        self.world, self.defaults = examples[name]; self.extensions = []; self.path = None
        self._refresh_lists(); self._write(f"Exemple chargé : {name}\nCliquez sur « Générer les extensions » pour lancer le calcul.")


def main():
    """Point d'entrée : crée l'application Qt, affiche la fenêtre et lance la boucle d'événements."""
    app = QApplication(sys.argv)
    app.setApplicationName("RCR — Logique des défauts")
    window = App(); window.show()
    sys.exit(app.exec())

if __name__ == "__main__":
    main()
