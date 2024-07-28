Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.

Require Import nbe.systemt.extensional.syntax.
Require Import nbe.systemt.extensional.semantic.

Definition SemTyp := D -> D -> Prop.

Definition SemTypTop (d d' : Dnf) : Prop :=
  forall n, exists w, Rⁿᶠ ⦇ n ⦈ d ↘ w /\ Rⁿᶠ ⦇ n ⦈ d' ↘ w.

Definition SemTypBot (e e' : Dne) : Prop :=
  forall n, exists u, Rⁿᵉ ⦇ n ⦈ e ↘ u /\ Rⁿᵉ ⦇ n ⦈ e' ↘ u.

Notation "e ≈ e' ∈ ⊥" := (SemTypBot e e')
  (at level 55, e' at next level, no associativity).

Notation "d ≈ d' ∈ ⊤" := (SemTypTop d d')
  (at level 55, d' at next level, no associativity).

Hint Constructors AppRel RNfRel RNeRel : core.

Lemma sem_bot_symm : forall e e',
  e ≈ e' ∈ ⊥ -> 
  e' ≈ e ∈ ⊥.
Proof.
  intros. unfold SemTypBot in *. intros.
  specialize (H n). destruct H as [u [Hrnee Hrene']].
  eauto.
Qed.

Lemma sem_bot_trans : forall e1 e2 e3,
  e1 ≈ e2 ∈ ⊥ -> 
  e2 ≈ e3 ∈ ⊥ -> 
  e1 ≈ e3 ∈ ⊥.
Proof.
  intros. unfold SemTypBot in *. intros.
  specialize (H n). specialize (H0 n).
  destruct H as [u1 [Hrnee1 Hrnee2]].
  destruct H0 as [u2 [Hrnee2' Hrnee3]].
  eapply rne_det in Hrnee2; eauto. subst. eauto.
Qed.

Lemma sem_typ_bot_var : forall i,
  (dne_l i) ≈ (dne_l i) ∈ ⊥.
Proof.
  intros. unfold SemTypBot. intros.
  exists (ne_v (n - i - 1)). split; eauto.
Qed.

Lemma sem_typ_bot_app : forall e e' d d',
  e ≈ e' ∈ ⊥ ->
  d ≈ d' ∈ ⊤ ->
  (dne_app e d) ≈ (dne_app e' d') ∈ ⊥.
Proof.
  intros. unfold SemTypBot in *. unfold SemTypTop in *. intros.
  specialize (H n).
  specialize (H0 n).
  destruct H as [u [Hrnee Hrnee']].
  destruct H0 as [w [Hrnfd Hrnfd']].
  exists (ne_app u w). intuition.
Qed.

Lemma sem_typ_top_ne : forall e e',
  e ≈ e' ∈ ⊥ ->
  dnf_reif ℕ (d_refl ℕ e) ≈ dnf_reif ℕ (d_refl ℕ e') ∈ ⊤.
Proof.
  intros. unfold SemTypTop. unfold SemTypBot in *. intros.
  specialize (H n).
  destruct H as [u [Hrnee Hrnee']].
  exists (nf_ne u). intuition.
Qed.

Lemma sem_bot_rec : forall e e' dz dz' ds ds' T,
  e ≈ e' ∈ ⊥ ->
  dz ≈ dz' ∈ ⊤ ->
  ds ≈ ds' ∈ ⊤ ->
  dne_rec T dz ds e ≈ dne_rec T dz' ds' e' ∈ ⊥.
Proof.
  intros. unfold SemTypBot in *. unfold SemTypTop in *.
  intros. specialize (H n). specialize (H0 n). specialize (H1 n).
  destruct H as [u [Hrnee Hrnee']].
  destruct H0 as [wz [Hrnfdz Hrnfdz']].
  destruct H1 as [ws [Hrnfds Hrnfds']].
  eauto.
Qed.

Lemma sem_top_zero : 
  (dnf_reif ℕ d_zero) ≈ (dnf_reif ℕ d_zero) ∈ ⊤.
Proof.
  unfold SemTypTop. intros; eauto.
Qed.

Lemma sem_top_suc : forall a a',
  (dnf_reif ℕ a) ≈ (dnf_reif ℕ a') ∈ ⊤ ->
  (dnf_reif ℕ (d_suc a)) ≈ (dnf_reif ℕ (d_suc a')) ∈ ⊤.
Proof.
  intros. unfold SemTypTop in *. intros.
  specialize (H n).
  destruct H as [w [Hrnfa Hrnfa']].
  eauto.
Qed.

Lemma sem_typ_top_abs : forall f f' S T,
  (forall e e', e ≈ e' ∈ ⊥ -> 
    exists b b', f ∙ (d_refl S e) ↘ b /\ f' ∙ (d_refl S e') ↘ b' /\ 
      (dnf_reif T b) ≈ (dnf_reif T b') ∈ ⊤) ->
  (dnf_reif (S → T) f) ≈ (dnf_reif (S → T) f') ∈ ⊤.
Proof.
  intros. unfold SemTypTop. intros.
  assert (dne_l n ≈ dne_l n ∈ ⊥) by (unfold SemTypBot; intros; eauto).
  apply H in H0.
  destruct H0 as [b [b']]. intuition.
  unfold SemTypTop in H3. specialize (H3 (1 + n)). destruct H3 as [w].
  exists (nf_abs w); intuition; eauto.
Qed.

Definition Realize (T : Typ) (A : SemTyp) : Prop :=
  (forall a a', A a a' -> dnf_reif T a ≈ dnf_reif T a' ∈ ⊤) /\
  (forall e e', e ≈ e' ∈ ⊥ -> A (d_refl T e) (d_refl T e')).

Notation "T ⊩ A" := (Realize T A)
  (at level 55, no associativity).

Inductive SemTypNat : D -> D -> Prop :=
  | snat_zero: SemTypNat d_zero d_zero
  | snat_suc : forall a a',
      SemTypNat a a' ->
      SemTypNat (d_suc a) (d_suc a')
  | snat_ne : forall e e',
      e ≈ e' ∈ ⊥ ->
      SemTypNat (d_refl ℕ e) (d_refl ℕ e').

Notation "'𝒩'" := SemTypNat.

Notation "a ≈ a' ∈ '𝒩'" := (SemTypNat a a')
  (at level 55, a' at next level, no associativity).

Lemma nat_realize_sem_nat : ℕ ⊩ 𝒩.
Proof.
  unfold Realize. split; intros.
  - induction H; unfold SemTypTop; intros; eauto.
    + unfold SemTypTop in IHSemTypNat. specialize (IHSemTypNat n).
      destruct IHSemTypNat as [w [Hrnfa Hrnfa']].
      eauto.
    + unfold SemTypBot in H. specialize (H n).
      destruct H as [u]. intuition. eauto.
  - constructor; auto.
Qed.

Definition SemArr (S T : SemTyp) : SemTyp :=
  fun f f' => forall a a', S a a' -> exists b b', f ∙ a ↘ b /\ f' ∙ a' ↘ b' /\ T b b'.

Notation "S ⇒ T" := (SemArr S T)  (at level 55, right associativity).

Lemma arr_realize_sem_arr : forall S T A B,
  S ⊩ A -> T ⊩ B -> 
  (S → T) ⊩ (A ⇒ B).
Proof.
  intros. unfold Realize in *. split.
  - intros. apply sem_typ_top_abs. intros. unfold SemArr in H1.  
    intuition.
    apply H4 in H2. apply H1 in H2. 
    destruct H2 as [b [b']]. exists b, b'. intuition.
  - intros. unfold SemArr. intros.
    exists (d_refl T (dne_app e (dnf_reif S a))), (d_refl T (dne_app e' (dnf_reif S a'))); intuition; eauto.
    + eauto using sem_typ_bot_app.
Qed.

Lemma sem_nat_symm : forall a a',
  a ≈ a' ∈ 𝒩 -> 
  a' ≈ a ∈ 𝒩.
Proof.
  intros.
  induction H; eauto using SemTypNat, sem_bot_symm.
Qed.

Lemma sem_nat_trans : forall a1 a2 a3,
  a1 ≈ a2 ∈ 𝒩 -> 
  a2 ≈ a3 ∈ 𝒩 -> 
  a1 ≈ a3 ∈ 𝒩.
Proof.
  intros. generalize dependent a3. induction H; intros; eauto.
  - dependent destruction H0.
    eauto using SemTypNat.
  - dependent destruction H0.
    eauto using SemTypNat, sem_bot_trans.
Qed.

Fixpoint interp_typ (T : Typ) : SemTyp :=
  match T with 
  | ℕ => 𝒩
  | S' → T' => (interp_typ S') ⇒ (interp_typ T')
  end.

Notation "⟦ T ⟧T" := (interp_typ T).

Notation "a ≈ a' ∈ ⟦ T ⟧T" := ((interp_typ T) a a') 
  (at level 55, a' at next level, no associativity).

Lemma sem_typ_symm: forall a a' T,
  a ≈ a' ∈ ⟦ T ⟧T ->
  a' ≈ a ∈ ⟦ T ⟧T.
Proof.
  intros. generalize dependent a. generalize dependent a'. induction T; intros.
  - simpl in *. apply sem_nat_symm. eauto.
  - simpl in *. unfold SemArr in *. intros.
    apply IHT1 in H0.
    apply H in H0.
    destruct H0 as [b [b']].
    exists b', b. intuition.
Qed.

Lemma sem_typ_trans : forall a1 a2 a3 T,
  a1 ≈ a2 ∈ ⟦ T ⟧T ->
  a2 ≈ a3 ∈ ⟦ T ⟧T ->
  a1 ≈ a3 ∈ ⟦ T ⟧T.
Proof.
  intros. generalize dependent a1. generalize dependent a2. generalize dependent a3.
  induction T; intros.
  - simpl in *. eapply sem_nat_trans; eauto.
  - simpl in *. unfold SemArr in *. intros.
    apply sem_typ_symm in H1 as H1'.
    eapply IHT1 in H1'; eauto.
    apply H in H1 as IH1.
    apply H0 in H1' as IH2.
    destruct IH1 as [b1 [b2]].
    destruct IH2 as [b2' [b3]].
    intuition.
    eapply app_det in H2; eauto. subst.
    exists b1, b3; intuition.
    eapply IHT2; eauto.
Qed.

Lemma sem_typ_refl : forall a a' T,
  a ≈ a' ∈ ⟦ T ⟧T ->
  a ≈ a ∈ ⟦ T ⟧T.
Proof.
  intros.
  eapply sem_typ_trans with (a2:=a'); eauto using sem_typ_symm.
Qed.

Lemma typ_realize_interp_typ : forall T,
  T ⊩ ⟦ T ⟧T.
Proof.
  intros. induction T.
  - apply nat_realize_sem_nat.
  - apply arr_realize_sem_arr; eauto.
Qed.

Lemma bot_subset_T : forall e e' T,
  e ≈ e' ∈ ⊥ ->
  d_refl T e ≈ d_refl T e' ∈ ⟦ T ⟧T.
Proof.
  intros. pose proof (typ_realize_interp_typ T).
  unfold Realize in H0. intuition.
Qed.

Lemma T_subset_top : forall a a' T,
  a ≈ a' ∈ ⟦ T ⟧T ->
  (dnf_reif T a) ≈ (dnf_reif T a') ∈ ⊤.
Proof.
  intros. pose proof (typ_realize_interp_typ T).
  unfold Realize in H0. intuition.
Qed.

Definition SemEqEnv (ρ ρ' : Env) (Γ : Ctx) :=
  forall i T, nth_error Γ i = Some T -> (ρ i) ≈ (ρ' i) ∈ ⟦ T ⟧T.

Notation "ρ ≈ ρ' ∈ ⟦ Γ ⟧Γ" := (SemEqEnv ρ ρ' Γ)
  (at level 55, ρ' at next level, no associativity).

Definition SemEqExp (Γ : Ctx) (t t' : Exp) (T : Typ) : Prop := 
  forall ρ ρ', ρ ≈ ρ' ∈ ⟦ Γ ⟧Γ -> exists a a', ⟦ t ⟧ ρ ↘ a /\ ⟦ t' ⟧ ρ' ↘ a' /\ a ≈ a' ∈ ⟦ T ⟧T.

Notation "Γ ⊨ t ≈ t' : T" := (SemEqExp Γ t t' T) 
  (at level 55, t at next level, t' at next level, no associativity).

Notation "Γ ⊨ t : T" := (SemEqExp Γ t t T)
  (at level 55, t at next level, no associativity).

Lemma sem_eq_env_symm : forall Γ ρ ρ',
  ρ ≈ ρ' ∈ ⟦ Γ ⟧Γ ->
  ρ' ≈ ρ ∈ ⟦ Γ ⟧Γ.
Proof.
  intros. unfold SemEqEnv in *. intros.
  apply H in H0. 
  apply sem_typ_symm; eauto.
Qed.

Lemma sem_eq_env_refl : forall Γ ρ ρ',
  ρ ≈ ρ' ∈ ⟦ Γ ⟧Γ ->
  ρ ≈ ρ ∈ ⟦ Γ ⟧Γ.
Proof.
  intros. unfold SemEqEnv in *. intros.
  eapply sem_typ_refl; eauto.
Qed.

Lemma sem_eq_env_trans : forall Γ ρ1 ρ2 ρ3,
  ρ1 ≈ ρ2 ∈ ⟦ Γ ⟧Γ ->
  ρ2 ≈ ρ3 ∈ ⟦ Γ ⟧Γ ->
  ρ1 ≈ ρ3 ∈ ⟦ Γ ⟧Γ.
Proof.
  intros. unfold SemEqEnv in *. intros.
  apply H in H1 as IH1.
  apply H0 in H1 as IH2.
  eauto using sem_typ_trans.
Qed.

Lemma sem_eq_exp_symm : forall Γ t t' T,
  Γ ⊨ t ≈ t' : T ->
  Γ ⊨ t' ≈ t : T.
Proof.
  intros. unfold SemEqExp in *. intros.
  apply sem_eq_env_symm in H0.
  apply H in H0. destruct H0 as [a [a']].
  exists a', a. intuition; eauto.
  apply sem_typ_symm; auto.
Qed.

Lemma sem_eq_exp_trans : forall Γ t1 t2 t3 T,
  Γ ⊨ t1 ≈ t2 : T ->
  Γ ⊨ t2 ≈ t3 : T ->
  Γ ⊨ t1 ≈ t3 : T.
Proof.
  intros. unfold SemEqExp in *. intros.
  apply H in H1 as IH1.
  apply sem_eq_env_symm in H1 as H1'.
  apply sem_eq_env_refl in H1'.
  apply H0 in H1' as IH2.
  destruct IH1 as [a1 [a2]].
  destruct IH2 as [a2' [a3]]. intuition.
  eapply eval_det in H2; eauto. subst.
  exists a1, a3; intuition.
  eapply sem_typ_trans; eauto.
Qed.

Definition SemEqSubst (Γ Δ : Ctx) (σ σ' : Subst) : Prop :=
  forall ρ ρ', ρ ≈ ρ' ∈ ⟦ Γ ⟧Γ -> exists τ τ', ⟦ σ ⟧s ρ ↘ τ /\ ⟦ σ' ⟧s ρ' ↘ τ' /\ τ ≈ τ' ∈ ⟦ Δ ⟧Γ.

Notation "Γ ⊨s σ ≈ σ' : Δ" := (SemEqSubst Γ Δ σ σ')
  (at level 55, σ at next level, σ' at next level, no associativity).

Notation "Γ ⊨s σ : Δ" := (SemEqSubst Γ Δ σ σ)
  (at level 55, σ at next level, no associativity).

Lemma sem_eq_subst_symm : forall Γ Δ σ σ',
  Γ ⊨s σ ≈ σ' : Δ ->
  Γ ⊨s σ' ≈ σ : Δ.
Proof.
  intros. unfold SemEqSubst in *. intros.
  apply sem_eq_env_symm in H0. apply H in H0.
  destruct H0 as [τ [τ']].
  exists τ', τ. intuition.
  apply sem_eq_env_symm. auto.
Qed.

Lemma sem_eq_subst_refl : forall Γ Δ σ σ',
  Γ ⊨s σ ≈ σ' : Δ ->
  Γ ⊨s σ ≈ σ : Δ.
Proof.
  intros. unfold SemEqSubst in *. intros.
  apply H in H0 as IH1.
  apply sem_eq_env_symm in H0.
  apply sem_eq_env_refl in H0.
  apply H in H0 as IH2.
  destruct IH1 as [τ11 [τ22]].
  destruct IH2 as [τ12 [τ22']].
  intuition. eapply subst_det in H2; eauto.
  subst.
  exists τ11, τ12. intuition.
  eauto using sem_eq_env_trans, sem_eq_env_symm.
Qed.

Lemma sem_eq_subst_trans : forall Γ Δ σ1 σ2 σ3, 
  Γ ⊨s σ1 ≈ σ2 : Δ ->
  Γ ⊨s σ2 ≈ σ3 : Δ ->
  Γ ⊨s σ1 ≈ σ3 : Δ.
Proof.
  intros. unfold SemEqSubst in *. intros.
  apply H in H1 as IH1.
  apply sem_eq_env_symm in H1.
  apply sem_eq_env_refl in H1.
  apply H0 in H1 as IH2.
  destruct IH1 as [τ1 [τ2]].
  destruct IH2 as [τ2' [τ3]].
  exists τ1, τ3. intuition; eauto.
  eapply subst_det in H2; eauto.
  subst. eapply sem_eq_env_trans; eauto.
Qed.

Hint Constructors EvalRel RecRel SubstRel : core.

Hint Constructors SemTypNat : core.

Lemma env_has_d : forall Γ i ρ ρ' T,
  nth_error Γ i = Some T ->
  ρ ≈ ρ' ∈ ⟦ Γ ⟧Γ ->
  exists a a', (ρ i) = a /\ (ρ' i = a') /\ a ≈ a' ∈ ⟦ T ⟧T.
Proof.
  intros. induction Γ.
  - destruct i; inversion H.
  - unfold SemEqEnv in H0. 
    apply H0 in H; eauto.
Qed.

Lemma sem_eq_exp_var : forall Γ i T,
  nth_error Γ i = Some T ->
  Γ ⊨ (exp_var i) ≈ (exp_var i) : T.
Proof.
  intros. unfold SemEqExp. intros.
  eapply env_has_d in H0; eauto.
  destruct H0 as [a [a']].
  exists a, a'; intuition.
  - rewrite <- H1; auto.
  - rewrite <- H0; auto.
Qed.

Lemma sem_eq_exp_zero : forall Γ,
  Γ ⊨ exp_zero ≈ exp_zero : ℕ.
Proof.
  intros. unfold SemEqExp. intros.
  exists d_zero, d_zero. intuition.
  simpl; eauto.
Qed.

Lemma sem_eq_exp_suc : forall Γ t t',
  Γ ⊨ t ≈ t' : ℕ ->
  Γ ⊨ (exp_suc t) ≈ (exp_suc t') : ℕ.
Proof.
  intros. unfold SemEqExp in *. intros.
  apply H in H0. destruct H0 as [a [a']].
  exists (d_suc a), (d_suc a'); simpl; intuition.
Qed.

Lemma sem_eq_exp_abs : forall Γ t t' S T,
  (S :: Γ) ⊨ t ≈ t' : T ->
  Γ ⊨ (λ t) ≈ (λ t') : S → T.
Proof.
  intros. unfold SemEqExp in *. intros.
  exists (d_abs t ρ), (d_abs t' ρ'); intuition.
  simpl. unfold SemArr. intros.
  assert ((ρ ↦ a) ≈ (ρ' ↦ a') ∈ ⟦ S :: Γ ⟧Γ). {
    unfold SemEqEnv in *. intros. destruct i; simpl in *; auto.
    - dependent destruction H2. auto.
  }
  apply H in H2. destruct H2 as [b [b']].
  exists b, b'; intuition.
Qed.

Lemma sem_eq_exp_app : forall Γ r r' s s' S T,
  Γ ⊨ r ≈ r' : S → T ->
  Γ ⊨ s ≈ s' : S ->
  Γ ⊨ r ▫ s ≈ r' ▫ s' : T.
Proof.
  intros. unfold SemEqExp in *. intros.
  apply H in H1 as IH1.
  apply H0 in H1 as IH2.
  destruct IH1 as [f [f']]. intuition.
  destruct IH2 as [a [a']]. intuition.
  simpl in H5. unfold SemArr in H5.
  apply H5 in H8.
  destruct H8 as [b [b']]. 
  exists b, b'; intuition; eauto.
Qed.

Lemma sem_eq_exp_shift : forall Γ i T S,
  nth_error Γ i = Some T ->
  (S :: Γ) ⊨ (exp_var i) [ ↑ ] ≈ exp_var (1 + i) : T.
Proof.
  intros. unfold SemEqExp in *.
  intros. unfold SemEqEnv in H0.
  exists (ρ (1 + i)), (ρ' (1 + i)). intuition; eauto.
  econstructor; eauto.
  replace (ρ (1 + i)) with ((drop ρ) i) by auto.
  eauto.
Qed.

Lemma sem_eq_exp_subst_id : forall Γ t T,
  Γ ⊨ t : T ->
  Γ ⊨ t [ es_id ] ≈ t : T.
Proof.
  intros. unfold SemEqExp in *.
  intros. apply H in H0.
  destruct H0 as [a [a']].
  exists a, a'. intuition; eauto.
Qed.

Lemma sem_eq_exp_subst_ext : forall Γ Δ σ s S,
  Γ ⊨s σ : Δ ->
  Γ ⊨ s : S ->
  Γ ⊨ (exp_var 0) [ es_ext σ s ] ≈ s : S.
Proof.
  intros. unfold SemEqExp in *. 
  unfold SemEqSubst in *.
  intros. apply H0 in H1 as IH1. destruct IH1 as [a [a']].
  apply H in H1 as IH2. destruct IH2 as [ρ1 [ρ1']].
  exists a, a'. intuition; eauto.
Qed.

Lemma sem_eq_exp_subst_shift : forall Γ Δ i σ s S T,
  Γ ⊨s σ : Δ ->
  Γ ⊨ s : S ->
  nth_error Δ i = Some T ->
  Γ ⊨ (exp_var (1 + i)) [ es_ext σ s ] ≈ (exp_var i) [ σ ] : T.
Proof.
  intros. unfold SemEqSubst in *. unfold SemEqExp in *. intros.
  apply H in H2 as IH1. destruct IH1 as [ρ1 [ρ1']].
  intuition.
  eapply env_has_d in H6 as IH2; eauto.
  destruct IH2 as [a [a']].
  apply H0 in H2 as IH2. destruct IH2 as [b [b']].
  exists a, a'. intuition.
  - econstructor; eauto.
    replace a with ((ρ1 ↦ b) (1 + i)). { econstructor. }
  - rewrite <- H7. eauto.
Qed.

Lemma sem_eq_exp_subst : forall Γ Δ t t' σ σ' T,
  Γ ⊨s σ ≈ σ' : Δ ->
  Δ ⊨ t ≈ t' : T -> 
  Γ ⊨ t [σ] ≈ t' [σ'] : T.
Proof.
  intros. unfold SemEqExp in *. unfold SemEqSubst in *. intros.
  apply H in H1 as IH2.
  destruct IH2 as [τ [τ']]. intuition.
  apply H0 in H5 as IH1.
  destruct IH1 as [a [a']].
  exists a, a'. intuition; eauto.
Qed.

Lemma sem_eq_exp_subst_comp : forall Γ1 Γ2 Γ3 τ σ t T,
  Γ1 ⊨s τ : Γ2 ->
  Γ2 ⊨s σ : Γ3 ->
  Γ3 ⊨ t : T ->
  Γ1 ⊨ t [σ] [τ] ≈ t [σ ∘ τ] : T.
Proof.
  intros. unfold SemEqExp in *. unfold SemEqSubst in *.
  intros.
  apply H in H2. destruct H2 as [ρ1 [ρ1']]. intuition.
  apply H0 in H5. destruct H5 as [ρ2 [ρ2']]. intuition.
  apply H1 in H7. destruct H7 as [a [a']]. exists a, a'. 
  intuition; eauto.
Qed.

Lemma sem_eq_exp_zero_subst : forall Γ Δ σ,
  Γ ⊨s σ : Δ ->
  Γ ⊨ exp_zero [σ] ≈ exp_zero : ℕ.
Proof.
  intros. unfold SemEqExp. intros.
  unfold SemEqSubst in *.
  apply H in H0.
  destruct H0 as [τ [τ']].
  exists d_zero, d_zero; simpl; intuition; eauto.
Qed.

Lemma sem_eq_exp_suc_subst : forall Γ Δ t σ,
  Γ ⊨s σ : Δ ->
  Δ ⊨ t : ℕ ->
  Γ ⊨ (exp_suc t) [σ] ≈ exp_suc (t [σ]) : ℕ.
Proof.
  intros. unfold SemEqExp in *. intros.
  unfold SemEqSubst in *.
  apply H in H1 as IH2. 
  destruct IH2 as [τ [τ']]. intuition.
  apply H0 in H5 as IH1.
  destruct IH1 as [a [a']].
  exists (d_suc a), (d_suc a'). intuition; simpl; eauto.
Qed.

Lemma sem_eq_exp_app_subst : forall Γ Δ r s σ S T, 
  Γ ⊨s σ : Δ ->
  Δ ⊨ r : S → T ->
  Δ ⊨ s : S ->
  Γ ⊨ (r ▫ s) [σ] ≈ (r [σ]) ▫ (s [σ]) : T.
Proof.
  intros. unfold SemEqExp in *. unfold SemEqSubst in *.
  intros.
  apply H in H2 as IH3. destruct IH3 as [τ [τ']]. intuition.
  apply H0 in H6 as IH1.
  apply H1 in H6 as IH2.
  destruct IH1 as [f [f']].
  destruct IH2 as [a [a']]. intuition.
  simpl in H11. unfold SemArr in H11.
  apply H11 in H12.
  destruct H12 as [b [b']].
  exists b, b'. intuition; eauto.
Qed.

Lemma sem_eq_exp_abs_eta : forall Γ t S T,
  Γ ⊨ t : S → T ->
  Γ ⊨ t ≈ ( λ (t [↑] ▫ (exp_var 0)) ) : S → T.
Proof.
  intros. unfold SemEqExp in *. intros.
  apply H in H0. destruct H0 as [a [a']].
  exists a, (d_abs (t [↑] ▫ exp_var 0) ρ'). intuition.
  simpl in *. unfold SemArr in *. intros.
  apply H3 in H2. destruct H2 as [b [b']].
  exists b, b'. intuition; eauto.
Qed.

Lemma sem_eq_exp_abs_beta : forall Γ t s S T,
  (S :: Γ) ⊨ t : T ->
  Γ ⊨ s : S ->
  Γ ⊨ ((λ t) ▫ s) ≈ t [es_ext es_id s] : T.
Proof.
  intros. unfold SemEqExp in *. intros.
  apply H0 in H1 as IH1.
  destruct IH1 as [a [a']]. intuition.
  assert (ρ ↦ a ≈ ρ' ↦ a' ∈ ⟦ S :: Γ ⟧Γ ). {
    simpl. unfold SemEqEnv in *. intros. destruct i; simpl in *; eauto.
    dependent destruction H4; eauto.
  }
  apply H in H4; eauto. destruct H4 as [b [b']].
  exists b, b'; intuition; eauto.
Qed.

Lemma sem_eq_exp_rec_zero : forall Γ tz ts T,
  Γ ⊨ tz : T ->
  Γ ⊨ ts : ℕ → T → T ->
  Γ ⊨ exp_rec T tz ts exp_zero ≈ tz : T.
Proof.
  intros. unfold SemEqExp in *. intros.
  apply H in H1 as IH1. destruct IH1 as [dz [dz']].
  apply H0 in H1 as IH2. destruct IH2 as [ds [ds']].
  exists dz, dz'. intuition; eauto.
Qed.

Lemma rec_rec : forall az az' aₛ aₛ' an an' T,
  az ≈ az' ∈ ⟦ T ⟧T ->
  aₛ ≈ aₛ' ∈ ⟦ ℕ → T → T ⟧T ->
  an ≈ an' ∈ ⟦ ℕ ⟧T ->
  exists a a', RecRel T az aₛ an a /\ RecRel T az' aₛ' an' a' /\ a ≈ a' ∈ ⟦ T ⟧T.
Proof.
  intros. simpl in H1. induction H1; auto.
  - exists az, az'; intuition; eauto.
  - destruct IHSemTypNat as [b [b']].
    simpl in *. unfold SemArr in H0. 
    apply H0 in H1. destruct H1 as [f [f']].
    intuition.
    apply H6 in H7. destruct H7 as [a1 [a1']].
    exists a1, a1'. intuition; eauto.
  - exists ( d_refl T (dne_rec T (dnf_reif T az) (dnf_reif (ℕ → T → T) aₛ) e)).
    exists ( d_refl T (dne_rec T (dnf_reif T az') (dnf_reif (ℕ → T → T) aₛ') e')). 
    intuition.
    eauto using sem_bot_rec, bot_subset_T, T_subset_top.
Qed.

Lemma sem_eq_exp_rec : forall Γ tz tz' ts ts' tn tn' T,
  Γ ⊨ tz ≈ tz' : T ->
  Γ ⊨ ts ≈ ts' : ℕ → T → T ->
  Γ ⊨ tn ≈ tn' : ℕ ->
  Γ ⊨ (exp_rec T tz ts tn) ≈ (exp_rec T tz' ts' tn') : T.
Proof.
  intros. unfold SemEqExp in *. intro.
  intros. apply H in H2 as IH1. apply H0 in H2 as IH2. apply H1 in H2 as IH3.
  destruct IH1 as [az [az']].
  destruct IH2 as [aₛ [aₛ']].
  destruct IH3 as [an [an']].
  intuition.
  eapply rec_rec in H11; eauto. destruct H11 as [b [b']].
  exists b, b'. intuition; eauto.
Qed.

Lemma sem_eq_exp_rec_suc : forall Γ tz ts tn T,
  Γ ⊨ tz : T ->
  Γ ⊨ ts : ℕ → T → T ->
  Γ ⊨ tn : ℕ ->
  Γ ⊨ exp_rec T tz ts (exp_suc tn) ≈ ts ▫ tn ▫ exp_rec T tz ts tn : T.
Proof.
  intros. unfold SemEqExp in *. intros.
  apply H in H2 as IH1.
  apply H0 in H2 as IH2.
  apply H1 in H2 as IH3.
  destruct IH1 as [az [az']].
  destruct IH2 as [aₛ [aₛ']].
  destruct IH3 as [an [an']]. intuition.
  eapply rec_rec in H11 as IH; eauto.
  destruct IH as [a1 [a1']]. intuition.
  simpl in *. unfold SemArr in H11.
  apply H11 in H12. destruct H12 as [f [f']]. intuition.
  apply H17 in H15. destruct H15 as [b1 [b1']].
  exists b1, b1'. intuition; eauto.
Qed.

Lemma sem_eq_exp_rec_subst : forall Γ Δ σ tz ts tn T,
  Γ ⊨s σ : Δ ->
  Δ ⊨ tz : T ->
  Δ ⊨ ts : ℕ → T → T ->
  Δ ⊨ tn : ℕ ->
  Γ ⊨ exp_rec T tz ts tn [σ] ≈ exp_rec T (tz [σ]) (ts [σ]) (tn [σ]) : T.
Proof.
  intros. unfold SemEqExp in *. unfold SemEqSubst in *.
  intros. 
  apply H in H3 as IH1. destruct IH1 as [ρ1 [ρ1']]. intuition.
  apply H0 in H7 as IH2.
  apply H1 in H7 as IH3.
  apply H2 in H7 as IH4. 
  destruct IH2 as [az [az']].
  destruct IH3 as [aₛ [aₛ']].
  destruct IH4 as [an [an']].
  intuition.
  eapply rec_rec in H15; eauto. destruct H15 as [a [a']].
  exists a, a'. intuition; eauto.
Qed.

Lemma sem_eq_exp_abs_subst : forall Γ Δ σ t S T,
  Γ ⊨s σ : Δ ->
  (S :: Δ) ⊨ t : T ->
  Γ ⊨ (λ t) [σ] ≈ (λ (t [es_ext (σ ∘ ↑) (exp_var 0)])) : S → T.
Proof.
  intros. unfold SemEqExp in *. unfold SemEqSubst in *.
  intros. apply H in H1 as IH1. destruct IH1 as [τ [τ']]. intuition; eauto.
  exists (d_abs t τ), (d_abs (t [es_ext (σ ∘ ↑) (exp_var 0)]) ρ'). 
  intuition; eauto.
  simpl. unfold SemArr. intros.
  assert ((τ ↦ a) ≈ (τ' ↦ a') ∈ ⟦ S :: Δ ⟧Γ). {
    simpl; unfold SemEqEnv; intros; destruct i; simpl in *; eauto.
    dependent destruction H6; eauto.
  }
  apply H0 in H6. destruct H6 as [b [b']].
  exists b, b'; intuition; eauto.
Qed.

Lemma sem_eq_subst_id_l : forall Γ σ Δ,
  Γ ⊨s σ : Δ ->
  Γ ⊨s es_id ∘ σ ≈ σ : Δ.
Proof.
  intros. unfold SemEqSubst in *. intros.
  apply H in H0; eauto. destruct H0 as [τ [τ']].
  exists τ, τ'. intuition; eauto.
Qed.

Lemma sem_eq_subst_id_r : forall Γ σ Δ,
  Γ ⊨s σ : Δ ->
  Γ ⊨s σ ∘ es_id ≈ σ : Δ.
Proof.
  intros. unfold SemEqSubst in *. intros.
  apply H in H0; eauto. destruct H0 as [τ [τ']].
  exists τ, τ'. intuition; eauto.
Qed.

Lemma sem_eq_subst_shift : forall Γ S,
  (S :: Γ) ⊨s ↑ ≈ ↑ : Γ.
Proof.
  intros. unfold SemEqSubst. intros. unfold SemEqEnv in H.
  exists (fun i => ρ (1 + i)), (fun i => ρ' (1 + i)); simpl; intuition; eauto.
  unfold SemEqEnv. intros.
  eapply H; eauto.
Qed.

Lemma sem_eq_subst_id : forall Γ,
  Γ ⊨s es_id : Γ.
Proof.
  intros. unfold SemEqSubst. intros. 
  exists ρ, ρ'. intuition; eauto.
Qed.

Lemma sem_eq_subst_ext : forall Γ Δ σ σ' s s' S,
  Γ ⊨s σ ≈ σ' : Δ ->
  Γ ⊨ s ≈ s' : S ->
  Γ ⊨s (es_ext σ s) ≈ (es_ext σ' s') : (S :: Δ).
Proof.
  intros. unfold SemEqSubst in *. unfold SemEqExp in *.
  intros.
  apply H in H1 as IH1.
  apply H0 in H1 as IH2.
  destruct IH1 as [τ [τ']].
  destruct IH2 as [a [a']].
  exists (τ ↦ a), (τ' ↦ a'). intuition; simpl; eauto.
  unfold SemEqEnv in *. intros. destruct i; simpl in H6; eauto.
  dependent destruction H6; auto.
Qed.

Lemma sem_eq_subst_comp : forall Γ1 Γ2 Γ3 σ σ' τ τ',
  Γ1 ⊨s σ ≈ σ' : Γ2 ->
  Γ2 ⊨s τ ≈ τ' : Γ3 ->
  Γ1 ⊨s (τ ∘ σ) ≈ (τ' ∘ σ') : Γ3.
Proof.
  intros. unfold SemEqSubst in *. intros.
  apply H in H1 as IH1. destruct IH1 as [ρ1 [ρ1']].
  intuition.
  apply H0 in H5 as IH2. destruct IH2 as [ρ2 [ρ2']].
  exists ρ2, ρ2'. intuition; eauto.
Qed.

Lemma sem_eq_subst_eta : forall Γ S,
  (S :: Γ) ⊨s es_id ≈ es_ext es_shift (exp_var 0) : (S :: Γ).
Proof.
  intros. unfold SemEqSubst. intros.
  unfold SemEqEnv in H. exists ρ, (drop ρ' ↦ ρ' 0). intuition; eauto.
  unfold SemEqEnv in *. intros. destruct i; simpl in *; auto.
Qed.

Lemma sem_eq_subst_prop : forall Γ1 Γ2 Γ3 σ τ s S,
  Γ1 ⊨s τ : Γ2 ->
  Γ2 ⊨s σ : Γ3 ->
  Γ2 ⊨ s : S ->
  Γ1 ⊨s (es_ext σ s) ∘ τ ≈ es_ext (σ ∘ τ) (s [τ]) : (S :: Γ3).
Proof.
  intros. unfold SemEqSubst in *. intros.
  unfold SemEqExp in *.
  apply H in H2 as IH1. destruct IH1 as [ρ1 [ρ1']].
  intuition.
  apply H0 in H6 as IH2. destruct IH2 as [ρ2 [ρ2']].
  apply H1 in H6 as IH3. destruct IH3 as [a [a']].
  intuition.
  exists (ρ2 ↦ a), (ρ2' ↦ a'). intuition; eauto.
  unfold SemEqEnv in *. intros. destruct i; simpl in *; eauto.
  dependent destruction H10; eauto.
Qed.

Lemma sem_eq_subst_ext_shift : forall Γ Δ σ s S,
  Γ ⊨s σ : Δ ->
  Γ ⊨ s : S ->
  Γ ⊨s ↑ ∘ (es_ext σ s) ≈ σ : Δ.
Proof.
  intros. unfold SemEqSubst in *. intros.
  unfold SemEqExp in *. 
  apply H in H1 as IH1.
  apply H0 in H1 as IH2.
  destruct IH1 as [ρ1 [ρ1']].
  destruct IH2 as [a [a']].
  exists ρ1, ρ1'. intuition; eauto.
Qed.

Lemma sem_eq_subst_assoc : forall Γ1 Γ2 Γ3 Γ4 σ1 σ2 σ3,
  Γ1 ⊨s σ1 : Γ2 ->
  Γ2 ⊨s σ2 : Γ3 ->
  Γ3 ⊨s σ3 : Γ4 ->
  Γ1 ⊨s (σ3 ∘ σ2) ∘ σ1 ≈ σ3 ∘ (σ2 ∘ σ1) : Γ4.
Proof.
  intros. unfold SemEqSubst in *. intros.
  apply H in H2 as IH1. destruct IH1 as [ρ1 [ρ1']].
  intuition.
  apply H0 in H6 as IH2. destruct IH2 as [ρ2 [ρ2']].
  intuition.
  apply H1 in H9 as IH3. destruct IH3 as [ρ3 [ρ3']].
  intuition.
  exists ρ3, ρ3'. intuition; eauto.
Qed.

Definition Nbe (n : nat) (ρ : Env) (t : Exp) (T: Typ) (w : Nf) :=
  exists a, ⟦ t ⟧ ρ ↘ a /\ Rⁿᶠ ⦇ n ⦈ (dnf_reif T a) ↘ w.

Definition Completenss' (n : nat) (ρ ρ' : Env) (s t : Exp) (T : Typ) :=
  exists w, Nbe n ρ s T w /\ Nbe n ρ' t T w.

Definition Completenss (n : nat) (ρ : Env) (s t : Exp) (T : Typ) :=
  exists w, Nbe n ρ s T w /\ Nbe n ρ t T w.

Lemma sem_eq_exp_completeness : forall Γ s t T ρ ρ' n,
  Γ ⊨ s ≈ t : T ->
  ρ ≈ ρ' ∈ ⟦ Γ ⟧Γ ->
  Completenss' n ρ ρ' s t T.
Proof.
  intros. unfold SemEqExp in *. apply H in H0.
  unfold Completenss. destruct H0 as [a [a']].
  intuition. apply T_subset_top in H3.
  unfold SemTypTop in H3.
  specialize (H3 n).
  destruct H3 as [w].
  exists w. split; unfold Nbe. 
  - exists a. intuition; eauto.
  - exists a'. intuition; eauto.
Qed.

Scheme typing_ind := Induction for Typing Sort Prop
  with subst_typing_ind := Induction for SubstTyping Sort Prop.

Combined Scheme typing_subst_typing_mutind from typing_ind, subst_typing_ind.

Lemma typing_subst_typing_sem_eq_exp_sem_eq_subst : 
  (forall Γ t T, Γ ⊢ t : T -> Γ ⊨ t : T) /\
  (forall Γ σ Δ, Γ ⊢s σ : Δ -> Γ ⊨s σ : Δ).
Proof.
  apply typing_subst_typing_mutind; intros; eauto.
  - apply sem_eq_exp_var; eauto.
  - apply sem_eq_exp_abs; eauto.
  - eapply sem_eq_exp_app; eauto.
  - apply sem_eq_exp_zero; auto.
  - apply sem_eq_exp_suc; auto.
  - apply sem_eq_exp_rec; auto.
  - eapply sem_eq_exp_subst; eauto.
  - apply sem_eq_subst_shift; auto.
  - apply sem_eq_subst_id; auto.
  - eapply sem_eq_subst_comp; eauto.
  - eapply sem_eq_subst_ext; eauto.
Qed.

Corollary typing_sem_eq_exp : forall Γ t T, 
  Γ ⊢ t : T -> 
  Γ ⊨ t : T.
Proof.
  specialize typing_subst_typing_sem_eq_exp_sem_eq_subst. intros; intuition.
Qed.

Corollary subst_typing_sem_eq_subst : forall Γ σ Δ,
  Γ ⊢s σ : Δ -> 
  Γ ⊨s σ : Δ.
Proof.
  specialize typing_subst_typing_sem_eq_exp_sem_eq_subst. intros; intuition.
Qed.

Scheme exp_eq_ind := Induction for ExpEq Sort Prop
  with subst_eq_ind := Induction for SubstEq Sort Prop.

Combined Scheme exp_eq_subst_eq_mutind from exp_eq_ind, subst_eq_ind.

Lemma sem_eq_exp_sem_eq_subst_sound : 
  (forall Γ s t T, Γ ⊢ s ≈ t : T -> Γ ⊨ s ≈ t : T) /\
  (forall Γ σ τ Δ, Γ ⊢s σ ≈ τ : Δ -> Γ ⊨s σ ≈ τ : Δ).
Proof with eauto using typing_sem_eq_exp, subst_typing_sem_eq_subst.
  apply exp_eq_subst_eq_mutind; intros.
  - eapply sem_eq_exp_abs_beta...
  - eapply sem_eq_exp_rec_zero...
  - eapply sem_eq_exp_rec_suc...
  - apply sem_eq_exp_shift...
  - apply sem_eq_exp_subst_id...
  - eapply sem_eq_exp_subst_ext...
  - eapply sem_eq_exp_subst_shift...
  - eapply sem_eq_exp_app_subst...
  - eapply sem_eq_exp_subst_comp...
  - eapply sem_eq_exp_zero_subst...
  - eapply sem_eq_exp_suc_subst...
  - eapply sem_eq_exp_rec_subst... 
  - apply sem_eq_exp_var...
  - eapply sem_eq_exp_app...
  - eapply sem_eq_exp_zero...
  - eapply sem_eq_exp_suc...
  - eapply sem_eq_exp_rec...
  - eapply sem_eq_exp_subst...
  - apply sem_eq_exp_symm...
  - eapply sem_eq_exp_trans...
  - apply sem_eq_exp_abs...
  - apply sem_eq_exp_abs_eta...
  - eapply sem_eq_exp_abs_subst...
  - eapply sem_eq_subst_ext_shift...
  - apply sem_eq_subst_id_l...
  - apply sem_eq_subst_id_r...
  - eapply sem_eq_subst_assoc...
  - eapply sem_eq_subst_eta...
  - eapply sem_eq_subst_prop...
  - apply sem_eq_subst_shift...
  - apply sem_eq_subst_id...
  - apply sem_eq_subst_ext...
  - eapply sem_eq_subst_comp...
  - apply sem_eq_subst_symm...
  - eapply sem_eq_subst_trans...
Qed.

Corollary syn_eq_exp_sem_eq_exp : forall Γ t t' T,
  Γ ⊢ t ≈ t' : T ->
  Γ ⊨ t ≈ t' : T.
Proof.
  specialize sem_eq_exp_sem_eq_subst_sound. intuition.
Qed.

Corollary syn_eq_subst_sem_eq_subst : forall Γ σ σ' Δ,
  Γ ⊢s σ ≈ σ' : Δ ->
  Γ ⊨s σ ≈ σ' : Δ.
Proof.
  specialize sem_eq_exp_sem_eq_subst_sound. intuition.
Qed.

Fixpoint init_env (Γ : Ctx) : Env :=
  match Γ with 
  | nil => fun i => d_zero 
  | T :: Γ' => fun i =>
                 match i with 
                 | 0 => d_refl T (dne_l (length Γ'))
                 | S i' => init_env Γ' i'
                 end
  end.

Lemma init_env_is_sem_env : forall Γ,
  init_env Γ ≈ init_env Γ ∈ ⟦ Γ ⟧Γ.
Proof.
  intros. induction Γ; simpl; auto.
  - unfold SemEqEnv. intros. destruct i; inversion H.
  - unfold SemEqEnv in *. intros. destruct i; simpl in *; auto.
    dependent destruction H. 
    apply bot_subset_T. unfold SemTypBot. intros; intuition; eauto.
Qed.

Theorem nbe_completness : forall Γ t T,
  Γ ⊢ t : T ->
  exists w, Nbe (length Γ) (init_env Γ) t T w.
Proof.
  intros. apply typing_sem_eq_exp in H.
  unfold SemEqExp in H. 
  pose proof (init_env_is_sem_env Γ). apply H in H0.
  destruct H0 as [a [a']]. intuition.
  eapply eval_det in H1; eauto. subst.
  apply T_subset_top in H3. unfold SemTypTop in H3.
  specialize (H3 (length Γ)). 
  destruct H3 as [w]. unfold Nbe.
  exists w, a. intuition.
Qed.

Theorem nbe_eq_completeness : forall Γ t t' T,
  Γ ⊢ t ≈ t' : T ->
  Completenss (length Γ) (init_env Γ) t t' T.
Proof.
  intros. apply syn_eq_exp_sem_eq_exp in H.
  pose proof (init_env_is_sem_env Γ).
  eapply sem_eq_exp_completeness in H; eauto.
Qed.
