Load PropLogic.
From Coq Require Import Setoids.Setoid.

Reserved Notation "U |- A" (at level 80).
Inductive Nd: list Proposition -> Proposition -> Prop :=
| Assumption U A (H: In A U): U |- A
| NotE U P (H1: U |- ¬ ¬ P) : U |- P
| NotI U P Q (H1: P::U |- Q) (H2: P::U |- ¬ Q): U |- ¬ P
| AndE1 U A B (H: U |- (A ∧ B)): U |- A
| AndE2 U A B (H: U |- (A ∧ B)): U |- B
| AndI U A B (H1: U |- A) (H2: U |- B): U |- (A ∧ B)
| OrE U P Q R (H1: U |- P ∨ Q) (H2: P :: U |- R) (H3: Q :: U |- R): U |- R
| OrI1 U P Q (H1: U |- P): U |- P ∨ Q
| OrI2 U P Q (H1: U |- P): U |- Q ∨ P
| ImpE U P Q (H1: U |- P) (H2: U |- P → Q): U |- Q
| ImpI U P Q (H: (P :: U)%list |- Q): U |- P → Q
where "U |- A" := (Nd U A).

Theorem p_implies_p: forall U p,
  U |- p → p.
Proof.
  intros.
  apply ImpI.
  apply Assumption.
  simpl.
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

Theorem principle_of_explosion: forall U p q,
  [p ; ¬ p] ++ U |- q.
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

Theorem material_implication: forall p q,
  [¬ p ∨ q] |- p → q.
Proof.
  intros.
  apply ImpI.
  apply (OrE _ ¬ p q).
  - apply Assumption. simpl. right. left. reflexivity.
  - apply NotE.
    apply (NotI _ _ p)
    ;apply Assumption
    ;simpl.
    + right. right. left. reflexivity.
    + right. left. reflexivity.
  - apply Assumption. simpl. left. reflexivity.
Qed.

Theorem NaturalDeduction_is_sound: forall Γ P,
  Γ |- P -> Γ |= P.
Proof.
  intros.
  induction H.
  - unfold models.
    intros.
    unfold Satisfies in H0.
    apply H0 in H.
    apply H.
  - unfold models in IHNd.
    unfold models.
    intros.
    destruct (valuation v P) eqn:E.
    + reflexivity.
    + apply IHNd in H0.
      simpl in H0.
      rewrite E in H0.
      simpl in H0.
      discriminate.
  - unfold models in IHNd1.
    unfold models in IHNd2.
    unfold models.
    simpl in IHNd2.
    intros v.
    destruct (valuation v P) eqn:E.
    + intros. apply (satisfy_chain _ U _) in E.
      * apply IHNd1 in E as IHNd1'.
        apply IHNd2 in E as IHNd2'.
        rewrite IHNd1' in IHNd2'.
        discriminate.
      * apply H1.
    + intros.
      simpl.
      rewrite E.
      simpl.
      reflexivity.
  - unfold models in IHNd.
    unfold models.
    intros.
    apply IHNd in H0.
    simpl in H0.
    apply and_both_true in H0.
    destruct H0 as [H0 _].
    apply H0.
  - unfold models in IHNd.
    unfold models.
    intros.
    apply IHNd in H0.
    simpl in H0.
    apply and_both_true in H0.
    destruct H0 as [_ H0].
    apply H0.
  - unfold models in IHNd1.
    unfold models in IHNd2.
    unfold models.
    intros.
    apply IHNd1 in H1 as IHNd1'.
    apply IHNd2 in H1 as IHNd2'.
    simpl.
    rewrite IHNd1'.
    rewrite IHNd2'.
    reflexivity.
  - unfold models in IHNd1.
    unfold models in IHNd2.
    unfold models in IHNd3. 
    unfold models.
    intros.
    apply IHNd1 in H2 as IHNd1'.
    simpl in IHNd1'.
    apply or_either_true in IHNd1'.
    destruct IHNd1' as [H3 | H3].
    + intros. apply (satisfy_chain _ U _) in H3.
      * apply IHNd2 in H3 as IHNd2'.
        apply IHNd2'.
      * apply H2.
    + intros. apply (satisfy_chain _ U _) in H3.
      * apply IHNd3 in H3 as IHNd3'.
        apply IHNd3'.
      * apply H2.
  - unfold models in IHNd.
    unfold models.
    intros.
    apply IHNd in H0.
    simpl.
    rewrite H0.
    simpl.
    reflexivity.
  - unfold models in IHNd.
    unfold models.
    intros.
    apply IHNd in H0.
    simpl.
    rewrite H0.
    destruct (valuation v Q);
    simpl; reflexivity.
  - unfold models in IHNd1.
    unfold models in IHNd2.
    unfold models.
    intros.
    apply IHNd1 in H1 as IHNd1'.
    apply IHNd2 in H1 as IHNd2'.
    simpl in IHNd2'.
    rewrite IHNd1' in IHNd2'.
    simpl in IHNd2'.
    apply IHNd2'.
  - unfold models in IHNd.
    unfold models.
    intros.
    simpl.
    destruct (valuation v P) eqn:E.
    + apply (satisfy_chain _ U _) in E.
      apply IHNd in E as IHNd'.
      rewrite IHNd'. simpl. reflexivity.
      apply H0.
    + simpl. reflexivity.
Qed.
