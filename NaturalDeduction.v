Load PropLogic.

Reserved Notation "U |- A" (at level 80).
Inductive Nd: list Proposition -> Proposition -> Prop :=
| Assumption U A (H: In A U): U |- A
| NotE U P (H: U |- ¬ (¬ P)): U |- P
| NotI U P Q (H1: U |- P) (H2: U |- Q) (H3: U |- ¬ Q): U |- ¬ P
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

Theorem and_introduction: forall p q,
  [p; q] |- p ∧ q.
Proof.
  intros p q.
  apply AndI.
  - apply Assumption. unfold In. left. reflexivity.
  - apply Assumption. unfold In. right. left. reflexivity.
Qed.

Theorem or_distributes_over_and: forall p q r,
  [(p∨(q∧r))] |- (p∨q)∧(p∨r).
Proof.
  intros p q r.
  apply AndI.
Abort.