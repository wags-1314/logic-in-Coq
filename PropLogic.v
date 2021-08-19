Parameter Atom : Type.

Inductive Proposition: Type := 
  | Atomic(P: Atom)
  | Negation(P: Proposition)
  | Conjunction(P Q: Proposition)
  | Disjunction(P Q: Proposition)
  | Implication(P Q: Proposition).

Notation "# P" := (Atomic P) (at level 1).
Notation "¬ P" := (Negation P) (at level 2).
Notation "P ∧ Q" := (Conjunction P Q) (at level 3).
Notation "P ∨ Q" := (Disjunction P Q) (at level 3).
Notation "P → Q" := (Implication P Q) (at level 4).





