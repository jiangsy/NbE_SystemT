Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Lia.

Require Import nbe.systemt.extensional.syntax.
Require Import nbe.systemt.extensional.semantic.
Require Import nbe.systemt.extensional.completeness.

Definition TypeStructure := Exp -> D -> Prop.

Definition KripkeTypeStructure := Ctx -> TypeStructure.

Fixpoint subst_from_weaken (Δ : Ctx) : Subst :=
  match Δ with
  | nil => es_id 
  | T :: Δ' => es_comp (subst_from_weaken Δ') es_shift
  end.

Hint Constructors SubstTyping : core.

Lemma subst_from_weaken_sound : forall Γ Δ,
  (Δ ++ Γ) ⊢s (subst_from_weaken Δ) : Γ.
Proof.
  intros. induction Δ; simpl in *; eauto.
Qed.

Fixpoint nf_to_exp (w : Nf) : Exp :=
  match w with 
  | nf_abs w' => exp_abs (nf_to_exp w')
  | nf_suc w' => exp_suc (nf_to_exp w')
  | nf_zero => exp_zero
  | nf_ne u => ne_to_exp u
  end
with ne_to_exp (u : Ne) : Exp :=
  match u with
  | ne_app u' w => exp_app (ne_to_exp u') (nf_to_exp w)
  | ne_rec T wz ws un => exp_rec T (nf_to_exp wz) (nf_to_exp ws) (ne_to_exp un)
  | ne_v i => exp_var i
  end.

Coercion nf_to_exp : Nf >-> Exp.
Coercion ne_to_exp : Ne >-> Exp.

Definition KripkeCandidateSpaceUpper (T : Typ) (Γ : Ctx) (t : Exp) (d : D) : Prop :=
  Γ ⊢ t : T /\
  forall Δ, exists w, Rⁿᶠ ⦇ length (Δ ++ Γ) ⦈ (dnf_reif T d) ↘ w /\ (Δ ++ Γ) ⊨ t [subst_from_weaken Δ] ≈ w : T.

Definition KripkeCandidateSpaceLower (T : Typ) (Γ : Ctx) (t : Exp) (e : Dne) : Prop :=
  Γ ⊢ t : T /\
  forall Δ, exists u, Rⁿᵉ ⦇ length (Δ ++ Γ) ⦈ e ↘ u /\ (Δ ++ Γ) ⊨ t [subst_from_weaken Δ] ≈ u : T.

Notation " t × d ∈ ⌈ T ⌉ ⦇ Γ ⦈" := (KripkeCandidateSpaceUpper T Γ t d)
  (at level 55, d at next level, T at next level, no associativity).

Notation " t × e ∈ ⌊ T ⌋ ⦇ Γ ⦈" := (KripkeCandidateSpaceLower T Γ t e)
  (at level 55, e at next level, T at next level, no associativity).

Lemma nat_lower_subset_upper : forall Γ t e,
  t × e ∈ ⌊ ℕ ⌋ ⦇ Γ ⦈ ->
  t × d_refl ℕ e ∈ ⌈ ℕ ⌉ ⦇ Γ ⦈.
Proof.  
  intros. unfold KripkeCandidateSpaceLower in *. unfold KripkeCandidateSpaceUpper in *. intros.
  intuition.
  specialize (H1 Δ).
  destruct H1 as [u]. intuition.
  exists (nf_ne u). intuition.
Qed.

Definition KripkeArrSpace (S T : Typ) (Γ : Ctx) (A B : KripkeTypeStructure): TypeStructure :=
  fun t f =>
    Γ ⊢ t : S → T /\
    forall Δ a s, A (Δ ++ Γ) s a -> exists b, f ∙ a ↘ b /\ B (Δ ++ Γ) (exp_app (t [subst_from_weaken Δ]) s) b.

Fixpoint interp_typ (T : Typ) : KripkeTypeStructure :=
  match T with 
  | ℕ => KripkeCandidateSpaceUpper ℕ
  | S' → T' => fun Γ => KripkeArrSpace S' T' Γ (interp_typ S') (interp_typ T')
  end.

Notation "t × d ∈ ⟦ T ⟧ ⦇ Γ ⦈" := ((interp_typ T) Γ t d)
  (at level 55, d at next level, T at next level, no associativity).

Lemma in_typ_structure_wf : forall Γ t T d,
  t × d ∈ ⟦ T ⟧ ⦇ Γ ⦈ -> Γ ⊢ t : T.
Proof.
  intros. generalize dependent t. generalize dependent d. generalize dependent Γ.
  induction T; intros; simpl in *.
  - unfold KripkeCandidateSpaceUpper in H. intuition.
  - unfold KripkeArrSpace in H. intuition.
Qed.

Lemma ext_length_ge : forall {A: Set} (Γ Δ : list A),
  length (Δ ++ Γ) >= length Γ.
Proof.
  intros. induction Δ; simpl; lia.
Qed.

Lemma ext_length_gt : forall {A: Set} (Γ Δ : list A) (T : A), 
  length (Δ ++ T :: Γ) > length Γ.
Proof.
  intros. specialize (ext_length_ge (T :: Γ) Δ). intros. simpl in *. lia. 
Qed.

Lemma var_in_typ_structure : forall Γ T,
  (exp_var 0) × (dne_l (length Γ)) ∈ ⌊ T ⌋ ⦇ T :: Γ ⦈.
Proof.
  intros. unfold KripkeCandidateSpaceLower. intuition.
  - econstructor. auto.
  - exists (ne_v ((length (Δ ++ T :: Γ)) - length Γ - 1)). split; eauto.
    induction Δ.
    Opaque Nat.sub.
    + simpl. replace (S (length Γ) - length Γ - 1) with 0 by lia.
      simpl. apply sem_eq_exp_subst_id.
      apply sem_eq_exp_var; auto.
    + simpl. eapply sem_eq_exp_trans with (t2:=exp_var 0 [subst_from_weaken Δ] [↑]).
      * apply sem_eq_exp_symm. eapply sem_eq_exp_subst_comp with (Γ2:=Δ ++ T :: Γ) (Γ3:= T :: Γ); eauto.
        apply sem_eq_subst_shift.
        apply subst_typing_sem_eq_subst. 
        eapply subst_from_weaken_sound.
        apply sem_eq_exp_var; eauto.
      * eapply sem_eq_exp_trans with (t2:=exp_var (length (Δ ++ T :: Γ) - length Γ - 1) [↑]).
        -- eapply sem_eq_exp_subst; eauto. eapply sem_eq_subst_shift.
        -- specialize (ext_length_gt Γ Δ T). intros.
           replace (S (length (Δ ++ T :: Γ)) - length Γ - 1) with (1 + (length (Δ ++ T :: Γ) - length Γ - 1)) by lia.
           eapply sem_eq_exp_shift; eauto.
           clear IHΔ. clear H. induction Δ; simpl.
           ++ replace (S (length Γ) - length Γ - 1) with 0 by lia. auto.
           ++ specialize (ext_length_gt Γ Δ T). intros.
              replace (S (length (Δ ++ T :: Γ)) - length Γ - 1) with (1 + (length (Δ ++ T :: Γ) - length Γ - 1)) by lia.
              simpl. auto.
Qed.

Lemma lower_subset_interp_typ_subset_upper : forall T Γ t,
  (forall e, t × e ∈ ⌊ T ⌋ ⦇ Γ ⦈ -> t × (d_refl T e) ∈ ⟦ T ⟧ ⦇ Γ ⦈) /\
  (forall d, t × d ∈ ⟦ T ⟧ ⦇ Γ ⦈  -> t × d ∈ ⌈ T ⌉ ⦇ Γ ⦈).
Proof.
  intro T. induction T; intros; split; intros.
  - simpl. apply nat_lower_subset_upper. auto.
  - auto.
  - simpl in *.
    unfold KripkeCandidateSpaceLower in H. intuition.
    unfold KripkeArrSpace. intuition.
   admit.
  - admit.
Admitted.