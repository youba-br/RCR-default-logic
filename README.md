# RCR-default-logic
RCR — PROJET : LOGIQUE DES DEFAUTS
Interface graphique : PyQt6 | Langage : Python 3

CONTENU
- app.py         : interface graphique PyQt6
- logic.py       : moteur logique indépendant de l'interface
- test_logic.py  : tests unitaires du moteur logique
- requirements.txt : dépendance de l'interface

INSTALLATION
1. Installer Python 3.10 ou une version plus récente.
2. Ouvrir un terminal dans le dossier RCR_MiniProjet.

3. Installer PyQt6 :
      python -m pip install -r requirements.txt

LANCEMENT
      python app.py



SYNTAXE DES FORMULES
- ~ : négation
- & : conjonction
- | : disjonction
- -> : implication
- <-> : équivalence
- Parenthèses autorisées
Exemples : p, ~q, p & q, p -> q, (p | q) -> r
Les expressions de prédicats telles que Oiseau(tweety) sont acceptées comme atomes.
Le projet ne réalise pas la quantification ni l'unification du premier ordre.

SAISIE D'UN DEFAUT
Prérequis : just1, just2 / conséquent
Dans l'interface, saisissez les trois champs séparément. Séparez les justifications par des virgules.

FONCTIONNALITES
- Ajouter/supprimer les formules de W et les défauts de D.
- Vérifier la cohérence du monde W.
- Générer les extensions de Reiter.
- Tester les conséquences sceptiques et crédules.
- Sauvegarder et recharger une théorie au format JSON, avec les extensions déjà calculées.
- Charger des exemples et lancer le diagnostic des justifications.
- Avertir immédiatement lors de l’ajout d’un défaut si une justification est
  individuellement incohérente (ex. : x & ~x), car le défaut ne sera jamais applicable.
- Signaler également les justifications individuellement cohérentes mais incompatibles
  entre elles.

NOTE TECHNIQUE
Le calcul des extensions repose sur une énumération des candidats puis une itération de Gamma. La complexité augmente exponentiellement avec le nombre de défauts ; une limite de sécurité est fixée dans logic.py.

