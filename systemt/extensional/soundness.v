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

Lemma typing_weaken : forall Γ Δ t T,
  Γ ⊢ t : T ->
  (Δ ++ Γ) ⊢ t [subst_from_weaken Δ] : T.
Proof.
  intros. econstructor; eauto using subst_from_weaken_sound.
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

Lemma list_concat_assoc : forall {A : Set} (Γ1 Γ2 Γ3 : list A),
  Γ1 ++ Γ2 ++ Γ3 = (Γ1 ++ Γ2) ++ Γ3.
Proof.
  intros. induction Γ1; auto.
  simpl. rewrite IHΓ1; auto.
Qed.

Lemma subst_from_weaken_comp : forall Γ Δ1 Δ2,
  (Δ1 ++ Δ2 ++ Γ) ⊨s subst_from_weaken Δ2 ∘ subst_from_weaken Δ1 ≈ subst_from_weaken (Δ1 ++ Δ2) : Γ.
Proof with eauto using typing_sem_eq_exp, subst_typing_sem_eq_subst, subst_from_weaken_sound, typing_weaken.
  intros. induction Δ1; simpl.
  - eapply sem_eq_subst_id_r... 
  - simpl. eapply sem_eq_subst_trans with (σ2:=(subst_from_weaken Δ2 ∘ subst_from_weaken Δ1) ∘ ↑)...
    apply sem_eq_subst_symm.
    eapply sem_eq_subst_assoc...
    eapply sem_eq_subst_comp; eauto.
    eapply sem_eq_subst_shift; eauto.
Qed.

Lemma lower_subset_interp_typ_subset_upper : forall T Γ t,
  (forall e, t × e ∈ ⌊ T ⌋ ⦇ Γ ⦈ -> t × (d_refl T e) ∈ ⟦ T ⟧ ⦇ Γ ⦈) /\
  (forall d, t × d ∈ ⟦ T ⟧ ⦇ Γ ⦈  -> t × d ∈ ⌈ T ⌉ ⦇ Γ ⦈).
Proof with eauto using typing_sem_eq_exp, subst_typing_sem_eq_subst, subst_from_weaken_sound, typing_weaken.
  intro T. induction T; intros; split; intros.
  - simpl. apply nat_lower_subset_upper. auto.
  - auto.
  - simpl in *.
    unfold KripkeCandidateSpaceLower in H. intuition.
    unfold KripkeArrSpace. intuition.
    exists (d_refl T2 (dne_app e (dnf_reif T1 a))). intuition.
    specialize (IHT2 (Δ ++ Γ) (t [subst_from_weaken Δ] ▫ s)).
    intuition. apply H2.
    unfold KripkeCandidateSpaceLower. intuition.
    eapply typing_app with (S:=T1)... 
    eapply in_typ_structure_wf; eauto. 
    specialize (H1 (Δ0 ++ Δ)). destruct H1 as [u].
    specialize (IHT1 (Δ ++ Γ) s). intuition.
    apply H5 in H. unfold KripkeCandidateSpaceUpper in H. intuition.
    specialize (H8 Δ0). destruct H8 as [w].
    exists (ne_app u w). intuition. econstructor; eauto.
    rewrite list_concat_assoc; auto.
    eapply sem_eq_exp_trans with (t2:=(t [subst_from_weaken Δ] [subst_from_weaken Δ0]) ▫ (s [subst_from_weaken Δ0])).
    eapply sem_eq_exp_app_subst with (Δ:=Δ ++ Γ); eauto...
    eapply sem_eq_exp_app; eauto. fold ne_to_exp.
    eapply sem_eq_exp_trans with (t2:=t [subst_from_weaken Δ ∘ subst_from_weaken Δ0]).
    eapply sem_eq_exp_subst_comp... 
    eapply sem_eq_exp_trans with (t2:=t [subst_from_weaken (Δ0 ++ Δ)]); eauto.
    eapply sem_eq_exp_subst...
    eapply subst_from_weaken_comp.
    rewrite list_concat_assoc. auto.
  - simpl in *. 
    unfold KripkeArrSpace in H. intuition.
    unfold KripkeCandidateSpaceUpper. intuition.
    pose proof (var_in_typ_structure (Δ ++ Γ) T1).
    replace (T1 :: Δ ++ Γ) with (T1 :: (Δ ++ Γ)) in H by auto.
    specialize (IHT1 (T1 ::Δ ++ Γ) (exp_var 0)). intuition. apply H2 in H.
    replace (T1 :: Δ ++ Γ) with ((T1 :: Δ) ++ Γ) in H by auto.
    apply H1 in H.
    destruct H as [b]. intuition.
    specialize (IHT2 ((T1 :: Δ) ++ Γ) (t [subst_from_weaken (T1 :: Δ)] ▫ (exp_var 0))). intuition.
    apply H6 in H5.
    unfold KripkeCandidateSpaceUpper in H5. intuition.
    specialize (H8 nil). destruct H8 as [w]... simpl in *. intuition.
    exists (nf_abs w). intuition; eauto.
    eapply sem_eq_exp_trans with (t2:=exp_abs ((t [subst_from_weaken Δ] [↑])  ▫ (exp_var 0))).
    eapply sem_eq_exp_abs_eta...
    eapply sem_eq_exp_abs. fold ne_to_exp. fold nf_to_exp.
    eapply sem_eq_exp_trans with (t2:=(t [subst_from_weaken Δ ∘ ↑] ▫ exp_var 0))...
    eapply sem_eq_exp_app with (S:=T1)...
    eapply sem_eq_exp_subst_comp...
    apply typing_sem_eq_exp... econstructor...
    eapply sem_eq_exp_trans with (t2:= (t [subst_from_weaken Δ ∘ ↑] ▫ exp_var 0) [es_id])...
    eapply sem_eq_exp_symm. eapply sem_eq_exp_subst_id...
Qed.

Corollary lower_subst_interp_typ : forall Γ e t T,
  t × e ∈ ⌊ T ⌋ ⦇ Γ ⦈ -> t × (d_refl T e) ∈ ⟦ T ⟧ ⦇ Γ ⦈.
Proof.
  intros.
  pose proof (lower_subset_interp_typ_subset_upper T Γ t). intuition.
Qed.

Corollary interp_typ_subset_upper : forall Γ a t T,
  t × a ∈ ⟦ T ⟧ ⦇ Γ ⦈  -> t × a ∈ ⌈ T ⌉ ⦇ Γ ⦈.
Proof.
  intros.
  pose proof (lower_subset_interp_typ_subset_upper T Γ t). intuition.
Qed.

Lemma syn_eq_exp_in_interp_typ : forall T Γ t t' a,
  Γ ⊢ t ≈ t' : T ->
  t × a ∈ ⟦ T ⟧ ⦇ Γ ⦈ ->
  t' × a ∈ ⟦ T ⟧ ⦇ Γ ⦈.
Proof with eauto using typing_sem_eq_exp, subst_typing_sem_eq_subst, subst_from_weaken_sound, typing_weaken.
  intro. induction T; intros.
  - simpl in *. unfold KripkeCandidateSpaceUpper in *. intuition.
    admit.
    pose proof (H2 Δ). destruct H0 as [w]. exists w. intuition.
    apply sem_eq_exp_trans with (t2:=t [subst_from_weaken Δ]); auto.
    eapply sem_eq_exp_subst... apply sem_eq_exp_symm... eapply syn_eq_exp_sem_eq_exp...
  - admit.
Admitted.
