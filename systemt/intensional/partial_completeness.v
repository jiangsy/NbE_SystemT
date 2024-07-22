Require Import Coq.Lists.List.
Require Import Coq.Program.Equality.

Require Import nbe.systemt.intensional.syntax.
Require Import nbe.systemt.intensional.semantic.

Definition SemTyp := D -> Prop.

Definition SemEnv := Env -> Prop.

Definition SemTypTop : SemTyp := 
  fun d => forall n, exists v, Rⁿᶠ ⦇ n ⦈ d ↘ v.

Notation "d ∈ ⊤" := (SemTypTop d)
  (at level 55, no associativity).

Definition SemTypBot : Dne -> Prop :=
 fun e => forall n, exists u, Rⁿᵉ ⦇ n ⦈ e ↘ u.

Notation "e ∈ ⊥" := (SemTypBot e)
  (at level 55, no associativity).

Reserved Notation "d ∈ '𝒩' "
  (at level 55, no associativity).
Inductive SemTypNat : SemTyp :=
 | st_nat_zero : d_zero ∈ 𝒩
 | st_nat_suc : forall d,
    d ∈ 𝒩 ->
    d_suc d ∈ 𝒩
 | st_nat_bot : forall e,
    e ∈ ⊥ ->
    SemTypNat (d_ne e)
where " d ∈ '𝒩' " := (SemTypNat d).

Definition SemTypArr : SemTyp -> SemTyp -> SemTyp :=
  fun A B f => forall a, A a -> exists b, B b /\ f ∙ a ↘ b.

Fixpoint interp_typ (T : Typ) : SemTyp :=
  match T with 
  | typ_nat => SemTypNat 
  | typ_arr S' T' => SemTypArr (interp_typ S') (interp_typ T')
  end.

Notation "⟦ T ⟧T" := (interp_typ T)
  (at level 55, no associativity).

Lemma bot_subset_T_subset_top : forall T,
  ( forall e, e ∈ ⊥ -> ⟦ T ⟧T (d_ne e) ) /\
  ( forall d, ⟦ T ⟧T d -> d ∈ ⊤ ).
Proof with eauto using SemTypNat, RNeRel, RNfRel.
  intros. induction T; split; try simpl...
  - intros. dependent induction H.
    + unfold SemTypTop. intros...
    + unfold SemTypTop in *.
      intros. specialize (IHSemTypNat n).
      destruct IHSemTypNat as [v]...
    + unfold SemTypTop in *. unfold SemTypBot in *.
      intros. specialize (H n).
      destruct H as [u]...
  - intros.
    unfold SemTypBot in *. 
    unfold SemTypArr. intros.
    exists (d_ne (dn_app e a)). split.
    + destruct IHT1. 
      destruct IHT2.
      apply H3. intros.
      apply H2 in H0. unfold SemTypTop in H0.
      specialize (H n).
      specialize (H0 n).
      destruct H as [u]. destruct H0 as [v]...
    + econstructor.
  - intros. unfold SemTypArr in *.
    unfold SemTypTop in *. intros. 
    destruct IHT1.
    destruct IHT2.
    specialize (H (d_ne (dn_l n))).
    assert ((⟦ T1 ⟧T) (d_ne (dn_l n))). {
      eapply H0. unfold SemTypBot. intros...
    }
    apply H in H4. destruct H4 as [b]. destruct H4 as [Hb Happ].
    dependent destruction Happ.
    + eapply H3 with (n:=S n) in Hb. 
      destruct Hb as [v]...
    + eapply H3 with (n:=n) in Hb.
      destruct Hb as [v]. dependent destruction H4.
      dependent destruction H4...
Qed.

Corollary bot_subset_T : forall e T, 
  e ∈ ⊥ -> 
  ⟦ T ⟧T (d_ne e).
Proof.
  specialize bot_subset_T_subset_top. intros. specialize (H T). intuition. 
Qed.

Corollary T_subset_top : forall d T, 
  ⟦ T ⟧T d -> 
  d ∈ ⊤.
Proof.
  specialize bot_subset_T_subset_top. intros. specialize (H T). intuition. 
Qed.
  
Definition SemApp (f a : D) (B : SemTyp) : Prop := 
  exists b, B b /\ f ∙ a ↘ b.

Definition SemRec (dz ds dn : D) (B : SemTyp) : Prop :=
  exists b, B b /\ rec( dz , ds , dn ) ↘ b.

Definition SemEval (t : Exp) (ρ : Env) (B : SemTyp) : Prop :=
  exists b, B b /\ ⟦ t ⟧ ρ ↘ b.

Fixpoint interp_ctx (Γ : Ctx) : SemEnv :=
  match Γ with 
  | nil => fun Δ => True
  | (T :: Γ') => fun Δ => ⟦ T ⟧T (Δ 0) /\ interp_ctx Γ' (drop Δ) 
  end.

Notation "⟦ Γ ⟧Γ" := (interp_ctx Γ)
  (at level 55, no associativity).

Definition SemTyping (Γ : Ctx) (t : Exp) (T : Typ) : Prop :=
  forall ρ, ⟦ Γ ⟧Γ ρ -> exists a, ⟦ t ⟧ ρ ↘ a /\ ⟦ T ⟧T a.

Notation "Γ ⊨ t : T" := (SemTyping Γ t T)
  (at level 55, t at next level, no associativity).

Lemma sem_typing_var_intro : forall Γ i T,
  nth_error Γ i = Some T ->
  Γ ⊨ (exp_var i) : T.
Proof.
  intros. generalize dependent i.
  induction Γ; intros.
  - destruct i; simpl in H; inversion H.
  - destruct i; simpl in H; eauto.
    + inversion H. subst. unfold SemTyping. intros. simpl in H0. 
      exists (ρ 0); split; eauto.
      * constructor.
      * intuition.
    + apply IHΓ in H.
      unfold SemTyping in *. intros.
      simpl in H0. intuition.
      apply H in H2. destruct H2 as [b [Heval Htyp]].
      exists b; split; eauto.
      dependent destruction Heval. unfold drop. econstructor.
Qed.

Lemma sem_typing_abs_intro : forall Γ t S T,
  (S :: Γ) ⊨ t : T ->
  Γ ⊨ (exp_abs t) : S → T.
Proof.
  intros. unfold SemTyping.
  intros. exists ((ƛ t) ρ). split.
  - econstructor.
  - unfold interp_typ; fold interp_typ.
    unfold SemTypArr. intros.
    unfold SemTyping in H.
    assert (⟦ S :: Γ ⟧Γ (ρ ↦ a))...
    + econstructor; auto.
    + apply H in H2. destruct H2 as [b [Heval Htyp]]...
      exists b; split; eauto.
      econstructor; eauto.
Qed.

Lemma sem_typing_suc_intro : forall Γ t,
  Γ ⊨ t : ℕ ->
  Γ ⊨ (exp_suc t) : ℕ.
Proof.
  intros. unfold SemTyping in *.
  intros. apply H in H0.
  destruct H0 as [a [Heval Htyp]].
  exists (d_suc a). split; eauto.
  eauto using EvalRel.
  unfold interp_typ in *.
  eauto using SemTypNat.
Qed.