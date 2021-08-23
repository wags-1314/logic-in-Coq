Load PropLogic.

Reserved Notation "U |- A" (at level 80).
Inductive Nd: list Proposition -> Proposition -> Prop :=
| Repeat U A (H: In A U): U |- A
| NotE U P (H: U |- ¬ (¬ P)): U |- P
| NotI U P Q (H1: U |- P) (H2: U |- Q) (H3: U |- ¬ Q): U |- ¬ P
| AndE1 U A B (H: U |- (A ∧ B)): U |- A
| AndE2 U A B (H: U |- (A ∧ B)): U |- B
| AndI U A B (H1: U |- A) (H2: U |- B): U |- (A ∧ B)
| OrE U P Q R (H1: U |- P ∨ Q) (H2: U |- P → R) (H3: U |- Q → R): U |- R
| OrI1 U P Q (H1: U |- P): U |- P ∨ Q
| OrI2 U P Q (H1: U |- P): U |- Q ∨ P
| ImpE U P Q (H1: U |- P) (H2: U |- P → Q): U |- Q
| ImpI U P Q (H: (P :: U)%list |- Q): U |- P → Q
where "U |- A" := (Nd U A).

Theorem and_is_commutative: forall Γ A B,
  Γ |- A ∧ B -> Γ |- B ∧ A.
Proof.
  intros Γ A B H1.
  apply (AndE1 Γ A B) in H1 as H2.
  apply (AndE2 Γ A B) in H1 as H3.
  apply (AndI Γ B A H3) in H2 as H4.
  apply H4.
Qed.

Example example_1: forall Γ P Q,
  ¬ P :: Q :: Γ |- ¬(P ∧ Q).
Proof.
  intros Γ P Q.
  apply (NotI _ _ P). Admitted.