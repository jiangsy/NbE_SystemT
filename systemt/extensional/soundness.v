Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Lia.
Require Import Setoid Morphisms.


Require Import nbe.systemt.extensional.list.
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

Hint Resolve subst_from_weaken_sound : core.

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
    forall Δ, exists w, Rⁿᶠ ⦇ length (Δ ++ Γ) ⦈ (dnf_reif T d) ↘ w /\ (Δ ++ Γ) ⊢ t [subst_from_weaken Δ] ≈ w : T.

Definition KripkeCandidateSpaceLower (T : Typ) (Γ : Ctx) (t : Exp) (e : Dne) : Prop :=
  Γ ⊢ t : T /\
    forall Δ, exists u, Rⁿᵉ ⦇ length (Δ ++ Γ) ⦈ e ↘ u /\ (Δ ++ Γ) ⊢ t [subst_from_weaken Δ] ≈ u : T.

Notation " t × d ∈ ⌈ T ⌉ ⦇ Γ ⦈" := (KripkeCandidateSpaceUpper T Γ t d)
  (at level 48, d at next level, T at next level, no associativity).

Notation " t × e ∈ ⌊ T ⌋ ⦇ Γ ⦈" := (KripkeCandidateSpaceLower T Γ t e)
  (at level 48, e at next level, T at next level, no associativity).

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
  (at level 48, d at next level, T at next level, no associativity).

Lemma in_typ_structure_wf : forall Γ t T d,
  t × d ∈ ⟦ T ⟧ ⦇ Γ ⦈ -> 
  Γ ⊢ t : T.
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

Hint Constructors Typing SubstTyping ExpEq SubstEq : core.

Lemma var_in_typ_structure : forall Γ T,
  (exp_var 0) × (dne_l (length Γ)) ∈ ⌊ T ⌋ ⦇ T :: Γ ⦈.
Proof.
  intros. unfold KripkeCandidateSpaceLower. intuition.
  - exists (ne_v ((length (Δ ++ T :: Γ)) - length Γ - 1)). split; eauto.
    induction Δ.
    Opaque Nat.sub.
    + simpl. replace (S (length Γ) - length Γ - 1) with 0 by lia.
      simpl. auto. 
    + simpl. eapply exp_eq_trans with (t2:=exp_var 0 [subst_from_weaken Δ] [↑]).
      * apply exp_eq_symm. eapply exp_eq_prop_comp with (Γ2:=Δ ++ T :: Γ) (Γ3:= T :: Γ); eauto.
      * eapply exp_eq_trans with (t2:=exp_var (length (Δ ++ T :: Γ) - length Γ - 1) [↑]); auto.
        -- eapply exp_eq_comp_subst; eauto. 
        -- specialize (ext_length_gt Γ Δ T). intros.
           replace (S (length (Δ ++ T :: Γ)) - length Γ - 1) with (1 + (length (Δ ++ T :: Γ) - length Γ - 1)) by lia. 
           apply exp_eq_subst_shift. auto.
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

Lemma sem_subst_eq_subst_from_weaken_comp : forall Γ Δ1 Δ2,
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

Lemma syn_subst_eq_subst_from_weaken_comp : forall Γ Δ1 Δ2,
  (Δ1 ++ Δ2 ++ Γ) ⊢s subst_from_weaken Δ2 ∘ subst_from_weaken Δ1 ≈ subst_from_weaken (Δ1 ++ Δ2) : Γ.
Proof with eauto using typing_sem_eq_exp, subst_typing_sem_eq_subst, subst_from_weaken_sound, typing_weaken.
  intros. induction Δ1; simpl.
  - eapply subst_eq_idr... 
  - simpl. eapply subst_eq_trans with (σ2:=(subst_from_weaken Δ2 ∘ subst_from_weaken Δ1) ∘ ↑)...
Qed.

Lemma lower_subset_interp_typ_subset_upper : forall T Γ t,
  (forall e, t × e ∈ ⌊ T ⌋ ⦇ Γ ⦈ -> t × (d_refl T e) ∈ ⟦ T ⟧ ⦇ Γ ⦈) /\
  (forall d, t × d ∈ ⟦ T ⟧ ⦇ Γ ⦈ -> t × d ∈ ⌈ T ⌉ ⦇ Γ ⦈).
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
    eapply exp_eq_trans with (t2:=(t [subst_from_weaken Δ] [subst_from_weaken Δ0]) ▫ (s [subst_from_weaken Δ0]))...
    eapply exp_eq_comp_app; eauto. fold ne_to_exp.
    eapply exp_eq_trans with (t2:=t [subst_from_weaken Δ ∘ subst_from_weaken Δ0])...
    eapply exp_eq_trans with (t2:=t [subst_from_weaken (Δ0 ++ Δ)]); eauto.
    eapply exp_eq_comp_subst...
    eapply syn_subst_eq_subst_from_weaken_comp.
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
    eapply exp_eq_trans with (t2:=exp_abs ((t [subst_from_weaken Δ] [↑])  ▫ (exp_var 0)))...
    eapply exp_eq_ext_xi. fold ne_to_exp. fold nf_to_exp.
    eapply exp_eq_trans with (t2:=(t [subst_from_weaken Δ ∘ ↑] ▫ exp_var 0))...
Qed.

Corollary lower_subst_interp_typ : forall Γ e t T,
  t × e ∈ ⌊ T ⌋ ⦇ Γ ⦈ -> 
  t × (d_refl T e) ∈ ⟦ T ⟧ ⦇ Γ ⦈.
Proof.
  intros.
  pose proof (lower_subset_interp_typ_subset_upper T Γ t). intuition.
Qed.

Corollary interp_typ_subset_upper : forall Γ a t T,
  t × a ∈ ⟦ T ⟧ ⦇ Γ ⦈ -> 
  t × a ∈ ⌈ T ⌉ ⦇ Γ ⦈.
Proof.
  intros.
  pose proof (lower_subset_interp_typ_subset_upper T Γ t). intuition.
Qed.

Lemma syn_eq_exp_in_interp_typ : forall T Γ t t' a,
  Γ ⊢ t ≈ t' : T ->
  t × a ∈ ⟦ T ⟧ ⦇ Γ ⦈ ->
  t' × a ∈ ⟦ T ⟧ ⦇ Γ ⦈.
Proof with eauto using ExpEq, SubstEq, typing_sem_eq_exp, subst_typing_sem_eq_subst, subst_from_weaken_sound, typing_weaken.
  intro. induction T; intros.
  - simpl in *. unfold KripkeCandidateSpaceUpper in *. intuition.
    eapply syn_exp_eq_typing_r; eauto.
    pose proof (H2 Δ). destruct H0 as [w]. exists w. intuition.
    apply exp_eq_trans with (t2:=t [subst_from_weaken Δ]); auto.
    eapply exp_eq_comp_subst...
  - simpl in *. unfold KripkeArrSpace in *. intuition.
    eapply syn_exp_eq_typing_r; eauto.
    apply H2 in H0 as IH1. destruct IH1 as [b]. exists b. intuition.
    eapply IHT2; eauto...
    eapply in_typ_structure_wf in H5 as IH2. dependent destruction IH2.
    eapply exp_eq_comp_app with (S:=T1); eauto...
    eapply exp_eq_comp_subst; eauto. 
    eapply typing_weaken with (Δ:=Δ) in H1.
    apply in_typ_structure_wf in H0 as IH3. apply exp_eq_refl; eauto.
Qed.

Lemma in_interp_typ_weaken : forall Δ T Γ t a,
  t × a ∈ ⟦ T ⟧ ⦇ Γ ⦈ -> 
  t [subst_from_weaken Δ] × a ∈ ⟦ T ⟧ ⦇ Δ ++ Γ ⦈.
Proof with eauto 4 using typing_sem_eq_exp, subst_typing_sem_eq_subst, subst_from_weaken_sound, typing_weaken, in_typ_structure_wf.
  intro Δ. induction Δ; simpl.
  - intros. eapply syn_eq_exp_in_interp_typ; eauto...
  - intro. induction T; auto.
    + simpl in *. unfold KripkeCandidateSpaceUpper in *. intuition...
      specialize (H1 (Δ0 ++ a :: Δ)). destruct H1 as [w].
      exists w. Opaque length. simpl_alist in *. intuition...
      eapply exp_eq_trans with (t2:=t [(subst_from_weaken Δ ∘ ↑) ∘ subst_from_weaken Δ0])...
      eapply exp_eq_prop_comp... simpl...
      eapply exp_eq_trans with (t2:=t [subst_from_weaken (Δ0 ++ one a ++ Δ)])...
      eapply exp_eq_comp_subst; eauto.
      eapply subst_eq_trans with (σ2:= subst_from_weaken (one a ++ Δ) ∘ subst_from_weaken Δ0); eauto.
      eapply subst_eq_compat_comp with (Γ2:=one a ++ Δ ++ Γ); simpl; eauto...
      apply subst_eq_refl... 
      replace (Δ0 ++ one a ++ Δ ++ Γ) with (Δ0 ++ (one a ++ Δ) ++ Γ). 
      eapply syn_subst_eq_subst_from_weaken_comp.
      simpl_alist. auto.
    + intros. simpl in *. unfold KripkeArrSpace in *.  intuition...
      specialize (H1 (Δ0 ++ a :: Δ)). simpl_alist in *. apply H1 in H as IH1.
      destruct IH1 as [b]. exists b. intuition.
      eapply syn_eq_exp_in_interp_typ; eauto.
      eapply exp_eq_comp_app with (S:=T1); eauto.
      eapply exp_eq_trans with (t2:=t [(subst_from_weaken Δ ∘ ↑) ∘ subst_from_weaken Δ0])...
      eapply exp_eq_comp_subst with (Δ:=Γ)... 
      eapply subst_eq_trans with (σ2:=subst_from_weaken (one a ++ Δ) ∘ subst_from_weaken Δ0)...
      eapply subst_eq_symm.
      replace (Δ0 ++ one a ++ Δ ++ Γ) with (Δ0 ++ (one a ++ Δ) ++ Γ) by (simpl_alist; auto).
      eapply syn_subst_eq_subst_from_weaken_comp.
      eapply subst_eq_compat_comp with (Γ2:=one a ++ Δ ++ Γ)...
      apply subst_eq_refl... simpl... apply subst_eq_refl...
      apply exp_eq_refl...
      apply exp_eq_symm.
      eapply exp_eq_prop_comp with (Γ2:=one a ++ Δ ++ Γ)... simpl...
      eapply exp_eq_refl.
      eapply in_typ_structure_wf...
Qed.

Definition FutureContext (Γ Δ : Ctx) (ρ : Env) (σ : Subst): Prop :=
  Δ ⊢s σ : Γ /\ (forall i T, nth_error Γ i = Some T -> (exp_var i) [ σ ] × (ρ i) ∈ ⟦ T ⟧ ⦇ Δ ⦈).

Notation "σ × ρ ∈ Δ ≤ Γ" := (FutureContext Γ Δ ρ σ)
  (at level 48, ρ at next level, Δ at next level, no associativity).

Definition ExpLogicalRel (Γ : Ctx) (t : Exp) (T : Typ) :=
  forall ρ σ Δ, σ × ρ ∈ Δ ≤ Γ -> exists a, ⟦ t ⟧ ρ ↘ a /\ (t [σ]) × a ∈ ⟦ T ⟧ ⦇ Δ ⦈.

Notation "Γ ⫢ t : T" := (ExpLogicalRel Γ t T)
  (at level 55, t at next level, no associativity).

Definition SubstLogicalRel (Γ Δ : Ctx) (σ : Subst) : Prop := 
  forall ρ' σ' Δ', σ' × ρ' ∈ Δ' ≤ Γ -> exists ρ, ⟦ σ ⟧s ρ' ↘ ρ /\ (σ ∘ σ') × ρ ∈ Δ' ≤ Δ.

Notation "Γ ⫢s σ : Δ" := (SubstLogicalRel Γ Δ σ)
  (at level 55, σ at next level, no associativity).

Lemma init_env_future_context : forall Γ,
  es_id × (init_env Γ) ∈ Γ ≤ Γ.
Proof with eauto using Typing, ExpEq.
  intros. unfold FutureContext. intuition. generalize dependent i. induction Γ; auto; intros.
  - destruct i; simpl in *; inversion H.
  - destruct i.
    + simpl in *. dependent destruction H. 
      eapply syn_eq_exp_in_interp_typ with (t:=exp_var 0).
      apply exp_eq_symm. apply exp_eq_subst_id...
      eapply lower_subst_interp_typ.
      eapply var_in_typ_structure.
    + simpl in H. apply IHΓ in H as IH.
      apply syn_eq_exp_in_interp_typ with (t:=exp_var (S i)).
      apply exp_eq_symm. apply exp_eq_subst_id...
      apply syn_eq_exp_in_interp_typ with (t:=exp_var i [ subst_from_weaken (one a) ])...
      simpl. eapply exp_eq_trans with (t2:=exp_var i [ ↑ ])...
      simpl_alist.
      apply in_interp_typ_weaken. simpl.
      apply syn_eq_exp_in_interp_typ with (t:=exp_var i [es_id])...
Qed.

Lemma exp_logical_rel_typing : forall Γ t T,
  Γ ⫢ t : T -> 
  Γ ⊢ t : T.
Proof.
  intros. unfold ExpLogicalRel in *.
  pose proof (init_env_future_context Γ). apply H in H0. 
  destruct H0 as [a]. intuition.
  apply in_typ_structure_wf in H2.
  dependent destruction H2. dependent destruction H0. auto.
Qed.

Lemma subst_logical_rel_subst_typing : forall Γ σ Δ,
  Γ ⫢s σ : Δ ->
  Γ ⊢s σ : Δ.
Proof.
  intros. unfold SubstLogicalRel in *. 
  pose proof (init_env_future_context Γ). apply H in H0. 
  destruct H0 as [ρ]. intuition. 
  unfold FutureContext in H2. intuition. 
  dependent destruction H0. dependent destruction H0_. auto.
Qed.

Hint Constructors EvalRel AppRel RecRel SubstRel RNeRel RNfRel Typing SubstTyping : core.

Lemma logical_rel_var : forall Γ i T,
  nth_error Γ i = Some T ->
  Γ ⫢ (exp_var i) : T.
Proof.
  intros. unfold ExpLogicalRel. intros. exists (ρ i). intuition.
  unfold FutureContext in H0. intuition.
Qed.

Lemma logical_rel_zero : forall Γ,
  Γ ⫢ exp_zero : ℕ.
Proof.
  intros. unfold ExpLogicalRel. intros. unfold FutureContext in H. intuition. 
  exists d_zero. intuition.
  apply syn_eq_exp_in_interp_typ with (t:=exp_zero). simpl.
  apply exp_eq_symm. eapply exp_eq_prop_zero; eauto. simpl.
  unfold KripkeCandidateSpaceUpper. intuition.
  exists nf_zero. intuition.
  eapply exp_eq_prop_zero; eauto.
Qed.

Lemma logical_rel_suc : forall Γ t,
  Γ ⫢ t : ℕ ->
  Γ ⫢ (exp_suc t) : ℕ.
Proof.
  intros. unfold ExpLogicalRel in *. intros.
  apply H in H0. destruct H0 as [a].
  exists (d_suc a). intuition. simpl in *. unfold KripkeCandidateSpaceUpper in *.
  intuition; eauto.
  dependent destruction H0.
  eapply syn_exp_eq_typing_l with (t':=exp_suc (t [σ])). eapply exp_eq_prop_suc; eauto.
  specialize (H3 Δ0). destruct H3 as [w].
  exists (nf_suc w). intuition; eauto.
  apply exp_eq_comp_suc in H4.
  apply exp_eq_trans with (t2:=exp_suc (t [σ]) [subst_from_weaken Δ0]); eauto.
  eapply exp_eq_comp_subst; eauto.
  dependent destruction H0.
  eapply exp_eq_prop_suc; eauto.
Qed.

(* Declare Instance Equivalence_eq (Γ : Ctx) (T : Typ) : Equivalence ((fun Γ T t t' => ExpEq Γ t t' T) Γ T).
Declare Instance Proper_Typing (Γ : Ctx) (T : Typ) : Proper (eq) ((fun Γ T t => Typing Γ t T) Γ T).
Declare Instance Proper_ExpLogicalRel (Γ : Ctx) (T : Typ) (a : D): Proper (eq) (fun t => (interp_typ T) Γ t a). *)

Lemma logical_rel_abs : forall Γ t S T,
  (S :: Γ) ⫢ t : T ->
  Γ ⫢ (λ t) : S → T.
Proof.
  intros. pose proof (exp_logical_rel_typing _ _ _ H) as Htyping. 
  unfold ExpLogicalRel in *. intros.
  exists (d_abs t ρ). intuition. simpl. unfold KripkeArrSpace. intuition.
  unfold FutureContext in H0. intuition. econstructor; eauto. 
  specialize (H (ρ ↦ a) (es_ext (σ ∘ subst_from_weaken Δ0) s) (Δ0 ++ Δ)).
  assert ((es_ext (σ ∘ subst_from_weaken Δ0) s) × (ρ ↦ a) ∈ (Δ0 ++ Δ) ≤ (S :: Γ)).
  {
    unfold FutureContext in H0. intuition.
    apply in_typ_structure_wf in H1 as Htyp.
    unfold FutureContext. intuition. 
    - eapply styping_ext; eauto.
    - destruct i; simpl in *. 
      + dependent destruction H0. eapply syn_eq_exp_in_interp_typ; eauto. 
      + eapply syn_eq_exp_in_interp_typ; eauto.
        apply H3 in H0 as IH. apply in_interp_typ_weaken with (Δ:=Δ0) in IH.
        eapply syn_eq_exp_in_interp_typ with (t:=exp_var i [σ] [subst_from_weaken Δ0]); eauto.
  } 
  apply H in H2. destruct H2 as [b]. exists b. intuition.
  unfold FutureContext in H0. intuition.
  apply in_typ_structure_wf in H1 as Htyp.
  eapply syn_eq_exp_in_interp_typ with (t:= exp_abs (t [(es_ext ((σ ∘ subst_from_weaken Δ0) ∘ ↑) (exp_var 0))]) ▫ s).
  eapply exp_eq_comp_app with (S:=S); eauto.
  eapply exp_eq_trans with (t2:=(λ t) [σ ∘ subst_from_weaken Δ0]); eauto.
  eapply syn_eq_exp_in_interp_typ with (t := (t [(es_ext ((σ ∘ subst_from_weaken Δ0) ∘ ↑) (exp_var 0))] [es_ext es_id s])). 
  apply exp_eq_symm. eapply exp_eq_beta_abs with (S:=S); eauto. eauto.  econstructor; eauto. eauto. 
  eapply syn_eq_exp_in_interp_typ with (t := t [(es_ext ((σ ∘ subst_from_weaken Δ0) ∘ ↑) (exp_var 0)) ∘ (es_ext es_id s)]); eauto.
  apply exp_eq_symm. eapply exp_eq_prop_comp with (Γ2 := S :: Δ0 ++ Δ); eauto. eauto.
  eapply syn_eq_exp_in_interp_typ with (t:= t [es_ext (σ ∘ subst_from_weaken Δ0) s]); eauto.
  eapply exp_eq_comp_subst with (Δ := S::Γ)...
  eapply subst_eq_trans with (σ2 := es_ext (((σ ∘ subst_from_weaken Δ0) ∘ ↑) ∘ es_ext es_id s) ((exp_var 0) [es_ext es_id s])).
  eapply subst_eq_compat_ext...
  eapply subst_eq_trans with (σ2 := (σ ∘ subst_from_weaken Δ0) ∘ (↑ ∘ es_ext es_id s)); eauto.
  eapply subst_eq_trans with (σ2 := (σ ∘ subst_from_weaken Δ0) ∘ es_id); eauto.
  eapply subst_eq_compat_comp; eauto. apply subst_eq_refl... econstructor; eauto.
  apply subst_eq_symm. eapply subst_eq_assoc with (Γ3:=S :: Δ0 ++ Δ); eauto. 
  eapply exp_eq_trans with (t2 := s [es_id]); eauto.
  apply subst_eq_symm. eapply subst_eq_prop with (Γ':=S :: Δ0 ++ Δ); eauto.
  eauto.
Qed.

Lemma logical_rel_rec : forall Γ ts tz tn T,
  Γ ⫢ tz : T ->
  Γ ⫢ ts : ℕ → T → T ->
  Γ ⫢ tn : ℕ ->
  Γ ⫢ exp_rec T tz ts tn : T.
Proof.
Admitted.

Ltac destruct_es_id := 
  repeat 
  match goal with 
  | H : ?Γ ⊢ ?t [ es_id ] : ?T |- _ => dependent destruction H
  | H : ?Γ ⊢s es_id : ?Δ |- _ => dependent destruction H
  end.

Lemma logical_rel_app : forall Γ r s S T,
  Γ ⫢ r : S → T ->
  Γ ⫢ s : S ->
  Γ ⫢ r ▫ s : T.
Proof.
  intros. unfold ExpLogicalRel in *. intros.
  apply H in H1 as IH1. destruct IH1 as [f]. intuition.
  simpl in H4. unfold KripkeArrSpace in H4. intuition.
  apply H0 in H1 as IH2. destruct IH2 as [a]. intuition.
  apply in_interp_typ_weaken with (Δ:=nil) in H7 as IH.
  apply H5 in IH. destruct IH as [b]. intuition.  exists b; intuition. 
  - eauto.
  - simpl in *.
    pose proof (init_env_future_context Γ). apply H0 in H4 as IH3. destruct IH3 as [a'].
    apply H in H4 as IH4. destruct IH4 as [f']. intuition. 
    unfold KripkeArrSpace in H14. intuition. destruct_es_id. 
    unfold FutureContext in H1. intuition. 
    intuition. apply in_typ_structure_wf in H13. destruct_es_id.
    eapply syn_eq_exp_in_interp_typ with (t:=(r [σ]) ▫ (s [σ])). 
    apply exp_eq_symm. eapply exp_eq_prop_app with (Δ:=Γ); eauto. 
    eapply syn_eq_exp_in_interp_typ with (t:=(r [σ] [es_id]) ▫ (s [σ] [es_id])); eauto.
Qed.

Lemma logical_rel_subst : forall Γ Δ t σ T,
  Γ ⫢s σ : Δ ->
  Δ ⫢ t : T ->
  Γ ⫢ t [ σ ] : T. 
Proof.
  intros. 
  apply exp_logical_rel_typing in H0 as Htyp.
  apply subst_logical_rel_subst_typing in H as Hsubst.
  unfold ExpLogicalRel in *. unfold SubstLogicalRel in *. intros. 
  apply H in H1 as IH1. destruct IH1 as [ρ']. intuition.
  apply H0 in H4 as IH2. destruct IH2 as [a]. intuition. 
  unfold FutureContext in H1. intuition. exists a. intuition. eauto.
  apply syn_eq_exp_in_interp_typ with (t := t [σ ∘ σ0]); eauto.
Qed.

Lemma subst_logical_rel_id : forall Γ,
  Γ ⫢s es_id : Γ.
Proof.
  intros. unfold SubstLogicalRel. intros. exists ρ'. intuition.
  unfold FutureContext in *. intuition.
  - eapply syn_subst_eq_subst_typing_l with (σ':=σ'). eauto.
  - eapply syn_eq_exp_in_interp_typ with (t:=exp_var i [σ']); eauto.
Qed.

Lemma subst_logical_rel_shift : forall Γ T,
  (T :: Γ) ⫢s ↑ : Γ.
Proof.
  intros. unfold SubstLogicalRel. intros. unfold FutureContext in H. intuition.
  exists (drop ρ'). intuition.
  unfold FutureContext. intuition. eauto.
  assert (nth_error (T :: Γ) (S i) = Some T0) by auto. apply H1 in H2.
  replace (drop ρ' i) with (ρ' (S i)) by auto.
  apply syn_eq_exp_in_interp_typ with (t := exp_var (S i) [σ']); eauto.
  eapply exp_eq_trans with (t2 := exp_var i [ ↑ ] [σ']); eauto.
  eapply exp_eq_comp_subst; eauto.
Qed.

Lemma subst_logical_rel_comp : forall Γ1 Γ2 Γ3 σ1 σ2,
  Γ1 ⫢s σ1 : Γ2 ->
  Γ2 ⫢s σ2 : Γ3 ->
  Γ1 ⫢s σ2 ∘ σ1 : Γ3.
Proof.
  intros. unfold SubstLogicalRel in *. intros.
  apply H in H1. destruct H1 as [ρ1]. intuition.
  apply H0 in H3. destruct H3 as [ρ2]. exists ρ2. intuition.
  econstructor; eauto. unfold FutureContext in *. intuition.
  - dependent destruction H1. dependent destruction H1_. eauto.
  - dependent destruction H1. dependent destruction H1_. apply H5 in H4 as IH. 
    apply syn_eq_exp_in_interp_typ with (t:=exp_var i [σ2 ∘ σ1 ∘ σ']); eauto.
Qed.

Lemma subst_logical_rel_ext : forall Γ Δ σ s S,
  Γ ⫢s σ : Δ ->
  Γ ⫢ s : S ->
  Γ ⫢s es_ext σ s : (S :: Δ).
Proof.
  intros.
  apply exp_logical_rel_typing in H0 as Htyp.
  apply subst_logical_rel_subst_typing in H as Hsubst.
  unfold SubstLogicalRel in *. intros.
  unfold ExpLogicalRel in *.  
  apply H in H1 as IH1. destruct IH1 as [ρ].
  apply H0 in H1 as IH2. destruct IH2 as [a].
  exists (ρ ↦ a). intuition. unfold FutureContext. intuition.
  - eapply styping_comp with (Γ2:=Γ); eauto.
    unfold FutureContext in H1. intuition.
  - unfold FutureContext in H5. intuition. 
    destruct i; simpl in *. 
    + dependent destruction H3. apply in_typ_structure_wf in H6 as Hwf. 
      unfold FutureContext in H1. intuition.
      eapply syn_eq_exp_in_interp_typ with (t:= s [ σ' ]); auto.
      eapply exp_eq_trans with (t2 := exp_var 0 [es_ext (σ ∘ σ') (s [ σ'])]); eauto.
      apply exp_eq_symm; eauto. 
      eapply exp_eq_comp_subst with (Δ:=T::Δ); eauto.
    + apply H8 in H3 as IH. apply in_typ_structure_wf in H6. unfold FutureContext in H1. intuition. 
      eapply syn_eq_exp_in_interp_typ with (t:=exp_var i [σ ∘ σ']); auto.
      eapply exp_eq_trans with (t2:=exp_var (Datatypes.S i) [es_ext (σ ∘ σ') (s [ σ' ])]); eauto.
      eapply exp_eq_comp_subst with (Δ:=S :: Δ); eauto.
Qed.

Lemma typing_subst_typing_exp_subst_logical_relation : 
  (forall Γ t T, Γ ⊢ t : T -> Γ ⫢ t : T) /\
  (forall Γ σ Δ, Γ ⊢s σ : Δ -> Γ ⫢s σ : Δ).
Proof with eauto.
  apply typing_subst_typing_mutind; intros.
  - apply logical_rel_var...
  - apply logical_rel_abs...
  - eapply logical_rel_app...
  - apply logical_rel_zero.
  - apply logical_rel_suc...
  - apply logical_rel_rec...
  - eapply logical_rel_subst...
  - eapply subst_logical_rel_shift...
  - eapply subst_logical_rel_id...
  - eapply subst_logical_rel_comp...
  - eapply subst_logical_rel_ext...
Qed.

Lemma typing_exp_logical_rel : forall Γ t T,
  Γ ⊢ t : T ->
  Γ ⫢ t : T.
Proof with eauto.
  pose proof typing_subst_typing_exp_subst_logical_relation. intuition.
Qed.

Lemma subst_typing_subst_logical_rel : forall Γ σ Δ,
  Γ ⊢s σ : Δ -> 
  Γ ⫢s σ : Δ.
Proof with eauto.
  pose proof typing_subst_typing_exp_subst_logical_relation. intuition.
Qed.