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

Hint Constructors EvalRel AppRel RecRel SubstRel RNfRel RNeRel SemTypNat : core.

Lemma sem_typing_var : forall Γ i T,
  nth_error Γ i = Some T ->
  Γ ⊨ (exp_var i) : T.
Proof.
  intros. generalize dependent i.
  induction Γ; intros.
  - destruct i; simpl in H; inversion H.
  - destruct i; simpl in H; eauto.
    + inversion H. subst. unfold SemTyping. intros. simpl in H0. 
      exists (ρ 0); split; eauto.
      * intuition.
    + apply IHΓ in H.
      unfold SemTyping in *. intros.
      simpl in H0. intuition.
      apply H in H2. destruct H2 as [b [Heval Htyp]].
      exists b; split; eauto.
      dependent destruction Heval. unfold drop. eauto.
Qed.

Lemma sem_typing_abs : forall Γ t S T,
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
    + simpl; split; auto.
    + apply H in H2. destruct H2 as [b [Heval Htyp]]...
      exists b; split; eauto.
Qed.

Lemma sem_typing_zero : forall Γ,
  Γ ⊨ exp_zero : ℕ.
Proof.
  intros. unfold SemTyping. intros.
  exists d_zero; split; simpl; auto. 
Qed.

Lemma sem_typing_suc : forall Γ t,
  Γ ⊨ t : ℕ ->
  Γ ⊨ (exp_suc t) : ℕ.
Proof.
  intros. unfold SemTyping in *.
  intros. apply H in H0.
  destruct H0 as [a [Heval Htyp]].
  exists (d_suc a). split; eauto.
  unfold interp_typ in *; auto.
Qed.

Lemma sem_typing_app : forall Γ r s S T,
  Γ ⊨ r : S → T ->
  Γ ⊨ s : S ->
  Γ ⊨ (exp_app r s) : T.
Proof.
  intros. unfold SemTyping in *. intros.
  apply H in H1 as Hf. 
  destruct Hf as [f [Hevalf Htypf]].
  apply H0 in H1 as Ha.
  destruct Ha as [a [Hevala Htypa]].
  simpl in Htypf. unfold SemTypArr in Htypf.
  apply Htypf in Htypa. destruct Htypa as [b [Hevalb Htypb]].
  exists b. split; auto.
  eauto.
Qed. 

Lemma sem_rec_rec : forall dz ds dn T,
  ⟦ T ⟧T dz ->
  ⟦ ℕ → T → T ⟧T ds ->
  ⟦ ℕ ⟧T dn ->
  SemRec dz ds dn (⟦ T ⟧T).
Proof.
  intros. induction H1; unfold SemRec in *; intros.
  - exists dz; eauto.
  - destruct IHSemTypNat as [dn [Htypn Hrecn]].
    simpl in H0. unfold SemTypArr in H0.
    apply H0 in H1. destruct H1 as [df [Htypf Happf]].
    apply Htypf in Htypn. destruct Htypn as [db [Htypb Happb]].
    eauto.
  - exists (d_ne (dn_rec dz ds e)). split; eauto.
    apply bot_subset_T. 
    apply T_subset_top in H.
    apply T_subset_top in H0.
    unfold SemTypBot in *.
    unfold SemTypTop in *. intros.
    specialize (H n). specialize (H0 n). specialize (H1 n).
    destruct H. destruct H0. destruct H1. eauto.
Qed.

Lemma sem_typing_rec : forall Γ tz ts tn T,
  Γ ⊨ tz : T ->
  Γ ⊨ ts : ℕ → T → T ->
  Γ ⊨ tn : ℕ ->
  Γ ⊨ exp_rec T tz ts tn : T.
Proof.
  intros. unfold SemTyping in *. intros.
  apply H1 in H2 as Hdn. destruct Hdn as [dn [Hevaln Htypn]]. 
  apply H in H2 as Hdz. destruct Hdz as [dz [Hevalz Htypz]].
  apply H0 in H2 as Hds. destruct Hds as [ds [Hevals Htyps]].
  eapply sem_rec_rec in Htyps; eauto.
  unfold SemRec in Htyps. destruct Htyps as [b [Hevalb Htypb]].
  exists b; eauto.
Qed.

Definition SemSubstTyping (Γ : Ctx) (σ : Subst) (Δ : Ctx) : Prop :=
  forall ρ, ⟦ Γ ⟧Γ ρ -> exists ρ', ⟦ σ ⟧s ρ ↘ ρ' /\ ⟦ Δ ⟧Γ ρ'.

Notation "Γ ⊨s σ : Δ" := (SemSubstTyping Γ σ Δ)
  (at level 55, σ at next level, no associativity).

Lemma sem_typing_subst : forall Γ Δ σ t T,
  Γ ⊨s σ : Δ ->
  Δ ⊨ t : T ->
  Γ ⊨ (exp_subst t σ) : T.
Proof.
  intros. unfold SemTyping in *.
  unfold SemSubstTyping in *. intros.
  apply H in H1 as Hsubst. destruct Hsubst as [ρ' [Heval Hsem]].
  apply H0 in Hsem.  
  destruct Hsem as [a [Hevala Htyp]].
  exists a. split; eauto.
Qed.

Lemma sem_subst_typing_shift : forall Γ S,
  (S :: Γ) ⊨s ↑ : Γ.
Proof.
  intros. unfold SemSubstTyping. intros.
  simpl in H. intuition. exists (drop ρ); split; eauto.
Qed.

Lemma sem_subst_typing_id : forall Γ,
  Γ ⊨s es_id : Γ.
Proof.
  intros. unfold SemSubstTyping. intros.
  exists ρ. intuition.
Qed.

Definition SemEqExp (Γ : Ctx) (t t' : Exp) (T : Typ) : Prop :=
  forall ρ, ⟦ Γ ⟧Γ ρ -> exists a a', ⟦ t ⟧ ρ ↘ a /\ ⟦ t' ⟧ ρ ↘ a' /\ ⟦ T ⟧T a /\ ⟦ T ⟧T a' /\ a = a'. 

Definition SemEqSubst (Γ : Ctx) (σ σ' : Subst) (Δ : Ctx) : Prop :=
  forall ρ, ⟦ Γ ⟧Γ ρ -> exists ρ1' ρ2', ⟦ σ ⟧s ρ ↘ ρ1' /\ ⟦ σ' ⟧s ρ ↘ ρ2' /\ ⟦ Δ ⟧Γ ρ1' /\ ⟦ Δ ⟧Γ ρ2' /\ ρ1' = ρ2'.