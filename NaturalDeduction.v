Load PropLogic.

Reserved Notation "U |- A" (at level 80).
Inductive Nd: list Proposition -> Proposition -> Prop :=
| Assumption U A (H: In A U): U |- A
| NotE U P (H1: U |- ¬ ¬ P) : U |- P
| NotI U P Q (H1: P::U |- Q) (H2: P::U |- ¬ Q): U |- ¬ P
| AndE1 U A B (H: U |- (A ∧ B)): U |- A
| AndE2 U A B (H: U |- (A ∧ B)): U |- B
| AndI U A B (H1: U |- A) (H2: U |- B): U |- (A ∧ B)
| OrE U P Q R (H1: U |- P ∨ Q) (H2: cons P U |- R) (H3: cons Q U |- R): U |- R
| OrI1 U P Q (H1: U |- P): U |- P ∨ Q
| OrI2 U P Q (H1: U |- P): U |- Q ∨ P
| ImpE U P Q (H1: U |- P) (H2: U |- P → Q): U |- Q
| ImpI U P Q (H: (P :: U)%list |- Q): U |- P → Q
where "U |- A" := (Nd U A).

Theorem p_implies_p: forall p,
  [] |- p → p.
Proof.
  intros.
  apply (ImpI _ p p).
  apply Assumption.
  unfold In.
  left.
  reflexivity.
Qed.

Example example_1': forall p q,
  [¬ p; q]|- ¬(p ∧ q).
Proof.
  intros p q.
  apply (NotI _ _ p).
  - apply (AndE1 _ _ q). apply Assumption. simpl. left. reflexivity.
  - apply Assumption. simpl. right. left. reflexivity.
Qed.

Example example_2': forall fire smoke rain,
  [fire → smoke; rain → ¬ smoke] |- rain → ¬ fire.
Proof.
  intros fire smoke rain.
  apply ImpI.
  apply (NotI _ _ smoke).
  - apply (ImpE _ fire _).
    + apply Assumption. simpl. left. reflexivity.
    + apply Assumption. simpl. right. right. left. reflexivity.
  - apply (ImpE _ rain _).
    + apply Assumption. simpl. right. left. reflexivity.
    + apply Assumption. simpl. right. right. right. left. reflexivity.
Qed.

Theorem principle_of_explosion: forall p q,
  [p ; ¬ p] |- q.
Proof.
  intros.
  apply NotE.
  apply (NotI _ _ p)
  ;apply Assumption
  ;simpl.
  - right. left. reflexivity.
  - right. right. left. reflexivity.
Qed.

Theorem law_of_excluded_middle: forall p,
  [] |- p ∨ ¬ p.
Proof.
  intros.
  apply NotE.
  apply (NotI _ _ ¬ p).
  - apply (NotI _ _ (p ∨ ¬ p)).
    + apply OrI1.
      apply Assumption.
      left.
      reflexivity.
    + apply Assumption. right. left. reflexivity.
  - apply (NotI _ _ (p ∨ ¬ p)).
    + apply OrI2.
      apply Assumption.
      left.
      reflexivity.
    + apply Assumption. right. left. reflexivity.
Qed.

Theorem double_not_introduction: forall p,
  [p] |- ¬ ¬ p.
Proof.
  intros p.
  apply (NotI _ _ p)
  ; apply Assumption
  ; simpl.
  - right. left. reflexivity.
  - left. reflexivity.
Qed.

Theorem contrapositve: forall p q,
  [p → q; ¬ q] |- ¬ p.
Proof.
  intros.
  apply (NotI _ _ q).
  - apply (ImpE _ p _)
    ; apply Assumption
    ; simpl.
    + left. reflexivity.
    + right. left. reflexivity.
  - apply Assumption.
    simpl.
    right. right. left.
    reflexivity.
Qed.