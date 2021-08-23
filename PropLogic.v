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

Fixpoint valuation v P: bool :=
  match P with
  | # P' => v P'
  | ¬ P' => negb (valuation v P')
  | P' ∧ Q' => andb (valuation v P') (valuation v Q')
  | P' ∨ Q' => orb (valuation v P') (valuation v Q')
  | P' → Q' => orb (negb (valuation v P')) (valuation v Q')
  end.

(* TODO: Logical Equivalence and Substitution *)

(* Satisfiability, Validity etc. *)

Definition satisfiable P: Prop := 
  exists v, valuation v P = true.

Definition valid P: Prop := 
  forall v, valuation v P = true.

Definition unsatisfiable P: Prop :=
  forall v, valuation v P = false.

Definition falsifiable P: Prop :=
  exists v, valuation v P = false.

Lemma negb_b_false_implies_b_true: forall b,
  negb b = false -> b = true.
Proof.
  intros.
  destruct b eqn:E.
  - reflexivity.
  - simpl in H. discriminate.
Qed. 

Theorem P_valid_iff_notP_unsatisfiable: forall P,
  valid P <-> unsatisfiable ¬ P.
Proof.
  unfold valid.
  unfold unsatisfiable.
  simpl.
  split.
  - intros. rewrite H. simpl. reflexivity.
  - intros. apply negb_b_false_implies_b_true. apply H.
Qed.

Theorem P_satisfiable_iff_notP_falsifiable: forall P,
  satisfiable P <-> falsifiable ¬ P.
Proof.
  unfold satisfiable.
  unfold falsifiable.
  split.
  - intros. destruct H as [v H]. exists v. simpl.
    rewrite H. reflexivity.
  - intros. destruct H as [v H]. exists v. simpl.
    simpl in H. apply negb_b_false_implies_b_true.
    apply H.
Qed.

Fixpoint models v (U: list Proposition) := 
  match U with
  | nil => true
  | (P :: U')%list => ((valuation v P) && (models v U'))%bool
  end.

Definition set_satisfiable U := 
  exists v, models v U = true.

Definition set_unsatisfiable U :=
  forall v, models v U = false.

Lemma b_andb_true_is_b: forall b,
  b = true -> (b && true)%bool = true.
Proof.
  intros.
  destruct b.
  - reflexivity.
  - discriminate.
Qed. 

Lemma b_andb_false_is_false: forall b,
  (b && false)%bool = false.
Proof.
  destruct b.
  - reflexivity.
  - reflexivity.
Qed. 
  
Theorem set_satisifable_cons_valid: forall U P,
  set_satisfiable U /\ valid P -> set_satisfiable (P :: U)%list.
Proof.
  unfold set_satisfiable.
  unfold valid.
  intros.
  destruct H as [[v H1] H2].
  exists v.
  destruct U.
  - simpl. rewrite H2. reflexivity.
  - simpl. simpl in H1. rewrite H1.
    apply b_andb_true_is_b. apply H2.
Qed.

Theorem unsatisfiable_cons_is_unsatisifiable: forall U P,
  set_unsatisfiable U -> set_unsatisfiable (P :: U)%list.
Proof.
  unfold set_unsatisfiable.
  intros.
  simpl.
  rewrite H.
  apply b_andb_false_is_false.
Qed.

Definition consequence U A := 
  forall v, models v U = true -> valuation v A = true.

Notation "U |= A" := (consequence U A) (at level 7).

Theorem consequence_cons: forall U A B,
  U |= A -> (B :: U)%list |= A.
Proof.
  unfold consequence.
  intros U A B H1 v H2.
  simpl in H2.
  apply H1.
  destruct (valuation v B) eqn:E.
  - simpl in H2. apply H2.
  - simpl in H2. discriminate.
Qed.

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | nil => False
  | cons x' l' => x' = x /\ In x l'
  end.

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

(* Natural Deduction *)



