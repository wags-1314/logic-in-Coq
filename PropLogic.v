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

Fixpoint In {A : Type} (x : A) (l : list A) : Prop :=
  match l with
  | nil => False
  | cons x' l' => x' = x \/ In x l'
  end.

Definition satisfiable P: Prop := 
  exists v, valuation v P = true.

Definition valid P: Prop := 
  forall v, valuation v P = true.

Definition unsatisfiable P: Prop :=
  forall v, valuation v P = false.

Definition falsifiable P: Prop :=
  exists v, valuation v P = false.

Definition Satisfies v Γ: Prop :=
  forall A, In A Γ -> valuation v A = true.

Fixpoint satisfies v Γ: bool :=
  match Γ with
  | nil => true
  | (p' :: Γ')%list => andb (valuation v p') (satisfies v Γ')
  end.

Theorem Satisfies_to_split: forall v Γ a,
  Satisfies v (a :: Γ)%list -> (valuation v a) = true /\ Satisfies v Γ.
Proof.
  unfold Satisfies.
  intros.
  split.
  - apply H.
    simpl.
    left.
    reflexivity.
  - intros.
    apply H.
    simpl.
    right.
    apply H0.
Qed. 

Theorem split_to_Satisfies: forall v Γ a,
  (valuation v a) = true /\ Satisfies v Γ -> Satisfies v (a::Γ)%list.
Proof.
  intros v Γ A [H1 H2].
  unfold Satisfies.
  intros.
  simpl in H.
  destruct H as [H | H].
  - rewrite <- H. apply H1.
  - unfold Satisfies in H2. apply H2.
    apply H.
Qed.  

Theorem satisfy_chain: forall v Γ A,
  (valuation v A) = true -> Satisfies v Γ -> Satisfies v (A :: Γ)%list.
Proof.
  intros.
  apply split_to_Satisfies.
  split.
  apply H.
  apply H0.
Qed.

Definition models Γ A: Prop :=
  forall v, Satisfies v Γ -> valuation v A = true.

Notation "Γ |= A" := (models Γ A) (at level 10).

Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).

Lemma and_both_true: forall p q,
  (p && q)%bool = true -> p = true /\ q = true.
Proof.
  destruct p, q;
  simpl;
  intros.
  - split; reflexivity.
  - discriminate.
  - discriminate.
  - discriminate.
Qed.

Lemma or_either_true: forall p q,
  (p || q)% bool = true -> p = true \/ q = true.
Proof.
  destruct p, q.
  simpl;
  intros.
  - left. reflexivity.
  - left. reflexivity.
  - right. reflexivity.
  - discriminate.
Qed.  


Theorem Satisfies_iff_satisfies: forall Γ v,
  Satisfies v Γ <-> satisfies v Γ = true.
Proof.
  intros.
  split.
  - induction Γ.
    + intros. simpl. reflexivity.
    + intros.
      simpl satisfies. 
      apply Satisfies_to_split in H.
      destruct H as [H1 H2].
      rewrite H1.
      simpl.
      apply IHΓ.
      apply H2.
  - induction Γ.
    simpl.
    + intros.
      unfold Satisfies.
      simpl.
      intros.
      inversion H0.
    + intros. apply split_to_Satisfies.
      split.
      * simpl in H.
        destruct (valuation v a).
        --  reflexivity.
        --  simpl in H.
            discriminate H.
      * apply IHΓ.
        simpl in H.
        apply and_both_true in H.
        destruct H as [_ H].
        apply H.
Qed.
        



