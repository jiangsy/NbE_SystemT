Require Import Coq.Program.Equality.
Require Import nbe.systemt.syntax.

Inductive D : Set :=
  | d_zero
  | d_suc (d : D)
  | d_abs (t : Exp) (ρ : nat -> D)
  | d_ne (dn : Dne)
with Dne : Set :=
  | dn_l (n : nat) 
  | dn_rec (z s : D) (dn : Dne)
  | dn_app (dn : Dne) (d : D).

Definition Env := nat -> D.

Definition add (ρ : Env) (d : D) : Env :=
  fun n => match n with 
    | 0 => d
    | S n => ρ n
    end.

Definition drop : Env -> Env :=
  fun ρ n => ρ (S n).

Notation "ρ ↦ d" := (add ρ d)
  (at level 48, left associativity).

Reserved Notation "f ∙ a ↘ b"
  (at level 55, a at next level, no associativity).
Reserved Notation "⟦ t ⟧ ρ ↘ a"
  (at level 55, ρ at next level, no associativity).
Reserved Notation "rec( dz , ds , dn ) ↘ d"
  (at level 55, ds at next level, dn at next level, no associativity).
Reserved Notation "⟦ σ ⟧s ρ ↘ ρ'"
  (at level 55, ρ at next level, no associativity).
Inductive AppRel : D -> D -> D -> Prop :=
  | app_abs : forall t ρ a b,
    ⟦ t ⟧ (ρ ↦ a) ↘ b ->
    (d_abs t ρ) ∙ a ↘ b
  | app_app : forall e d,
    (d_ne e) ∙ d ↘ (d_ne (dn_app e d))
with EvalRel : Exp -> Env -> D -> Prop :=
  | eval_var : forall ρ n,
    ⟦ exp_var n ⟧ ρ ↘ (ρ n)
  | eval_abs : forall ρ t,
    ⟦ exp_abs t ⟧ ρ ↘ (d_abs t ρ)
  | eval_app : forall ρ r s f a b,
    ⟦ r ⟧ ρ ↘ f ->
    ⟦ s ⟧ ρ ↘ a ->
    f ∙ a ↘ b ->
    ⟦ exp_app r s ⟧ ρ ↘ b
  | eval_ze : forall ρ,
    ⟦ exp_zero ⟧ ρ ↘ d_zero
  | eval_suc : forall ρ t d,
    ⟦ t ⟧ ρ ↘ d ->
    ⟦ exp_suc t ⟧ ρ ↘ (d_suc d)
  | eval_rec : forall ρ ez es en dz ds dn a T,
    ⟦ ez ⟧ ρ ↘ dz ->
    ⟦ es ⟧ ρ ↘ ds -> 
    ⟦ en ⟧ ρ ↘ dn ->
    rec( dz , ds , dn ) ↘ a ->
    ⟦ exp_rec T ez es en ⟧ ρ ↘ a (* see p.p 32 : annotate recursion with type T *) 
  | eval_subst : forall ρ ρ' t σ a,
    ⟦ σ ⟧s ρ ↘ ρ' ->
    ⟦ t ⟧ ρ' ↘ a ->
    ⟦ exp_subst t σ ⟧ ρ' ↘ a
with RecRel : D -> D -> D -> D -> Prop :=
  | rec_ze : forall dz ds, 
    rec( dz , ds , d_zero ) ↘ dz
  | rec_suc : forall dz ds dn f a b,
    rec( dz , ds , dn) ↘ a ->
    ds ∙ dn ↘ f ->
    f ∙ a ↘ b ->
    rec( dz , ds , d_suc dn ) ↘ b
  | rec_rec : forall dz ds dn,
    rec( dz , ds , d_ne dn) ↘ d_ne (dn_rec dz ds dn)
with SubstRel : Subst -> Env -> Env -> Prop :=
  | subst_shift : forall ρ,
    ⟦ ↑ ⟧s ρ ↘ (drop ρ)
  | subst_id : forall ρ,
    ⟦ es_id ⟧s ρ ↘ ρ
  | subst_comp : forall ρ ρ' ρ'' σ1 σ2,
    ⟦ σ2 ⟧s ρ ↘ ρ' ->
    ⟦ σ1 ⟧s ρ' ↘ ρ'' ->
    ⟦ σ1 ∘ σ2 ⟧s ρ ↘ ρ''
  | psusbt_ext : forall ρ ρ' σ t a,
    ⟦ σ ⟧s ρ ↘ ρ' ->
    ⟦ t ⟧ ρ ↘ a -> (* why not ρ', but ρ *)
    ⟦ es_ext σ t ⟧s ρ ↘ (ρ ↦ a)
where "f ∙ a ↘ b" := (AppRel f a b) and 
      "⟦ t ⟧ ρ ↘ a" := (EvalRel t ρ a) and 
      "rec( dz , ds , dn ) ↘ d" := (RecRel dz ds dn d) and 
      "⟦ σ ⟧s ρ ↘ ρ'" := (SubstRel σ ρ ρ').

Scheme app_ind := Induction for AppRel Sort Prop
  with eval_ind := Induction for EvalRel Sort Prop
  with rec_ind := Induction for RecRel Sort Prop 
  with subst_ind := Induction for SubstRel Sort Prop.

Combined Scheme app_eval_rec_subst_mutind from app_ind, eval_ind, rec_ind, subst_ind.

Lemma app_eval_rec_subst_det : 
  ( forall f a b1, f ∙ a ↘ b1 -> forall b2, f ∙ a ↘ b2 ->  b1 = b2 ) /\
  ( forall t ρ a1, ⟦ t ⟧ ρ ↘ a1 -> forall a2, ⟦ t ⟧ ρ ↘ a2 -> a1 = a2 ) /\
  ( forall dz ds dn d1, rec( dz , ds , dn ) ↘ d1 -> forall d2,  rec( dz , ds , dn ) ↘ d2 -> d1 = d2 ) /\
  ( forall σ ρ ρ1', ⟦ σ ⟧s ρ ↘ ρ1' -> forall ρ2', ⟦ σ ⟧s ρ ↘ ρ2' -> ρ1' = ρ2' ).
Proof.
  apply app_eval_rec_subst_mutind; intros.
  - dependent destruction H0; auto.
  - dependent destruction H; auto.
  - dependent destruction H; auto.
  - dependent destruction H; auto.
  - dependent destruction H2.
    + apply H in H2_. 
      apply H0 in H2_0. subst.
      apply H1 in H2. auto.
  - dependent destruction H. auto.
  - dependent destruction H0. 
    apply f_equal. eauto.
  - dependent destruction H3. eauto.
    apply H in H3_.
    apply H0 in H3_0.
    apply H1 in H3_1.
    subst. eauto.
  - dependent destruction H1.
    eauto.
  - dependent destruction H. auto.
  - dependent destruction H2.
    apply H0 in H3. subst.
    apply H in H2. subst.
    eauto.
  - dependent destruction H. auto.
  - dependent destruction H. auto.
  - dependent destruction H. auto.
  - dependent destruction H1.
    apply H in H1_. subst. eauto.
  - dependent destruction H1. 
    apply H0 in H2. subst. eauto.
Qed.

Theorem app_det : forall f a b1 b2, 
  f ∙ a ↘ b1 -> 
  f ∙ a ↘ b2 -> 
  b1 = b2.
Proof. 
  specialize app_eval_rec_subst_det. intuition. eauto.
Qed.

Theorem eval_det : forall t ρ a1 a2, 
  ⟦ t ⟧ ρ ↘ a1 -> 
  ⟦ t ⟧ ρ ↘ a2 -> 
  a1 = a2.
Proof. 
  specialize app_eval_rec_subst_det. intuition. eauto.
Qed.

Theorem rec_det : forall dz ds dn d1 d2, 
  rec( dz , ds , dn ) ↘ d1 -> 
  rec( dz , ds , dn ) ↘ d2 -> 
  d1 = d2.
Proof.  
  specialize app_eval_rec_subst_det. intuition. eauto.
Qed.

Theorem subst_det : forall σ ρ ρ1' ρ2', 
  ⟦ σ ⟧s ρ ↘ ρ1' -> 
  ⟦ σ ⟧s ρ ↘ ρ2' -> 
  ρ1' = ρ2'.
Proof.
  specialize app_eval_rec_subst_det. intuition. eauto.
Qed.

Reserved Notation " 'Rⁿᶠ' ⦇ n ⦈ d ↘ v"
  (at level 55, d at next level, no associativity).
Reserved Notation " 'Rⁿᵉ' ⦇ n ⦈ e ↘ u"
  (at level 55, e at next level, no associativity).
Inductive RNfRel : nat -> D -> Intensional.Nf -> Prop :=
  | rnf_abs : forall t ρ v b n,
    ⟦ t ⟧ ( ρ ↦ d_ne (dn_l n)) ↘ b ->
    Rⁿᶠ ⦇ S n ⦈ b ↘ v ->
    Rⁿᶠ ⦇ n ⦈ (d_abs t ρ) ↘ (Intensional.nf_abs v)
  | rnf_ne : forall n e u,
    Rⁿᵉ ⦇ n ⦈ e ↘ u ->
    Rⁿᶠ ⦇ n ⦈ (d_ne e) ↘ (Intensional.nf_ne u)
  | rnf_zero : forall n,
    Rⁿᶠ ⦇ n ⦈ (d_zero) ↘ (Intensional.nf_zero)
  | rnf_suc : forall d v n,
    Rⁿᶠ ⦇ n ⦈ d ↘ v ->
    Rⁿᶠ ⦇ n ⦈ (d_suc d) ↘ (Intensional.nf_suc v)
with RNeRel : nat -> Dne -> Intensional.Ne -> Prop :=
  | rne_v : forall n k,
    Rⁿᵉ ⦇ n ⦈ (dn_l k) ↘ (Intensional.ne_v (n - k - 1))
  | rne_app : forall n e d u v,
    Rⁿᵉ ⦇ n ⦈ e ↘ u ->
    Rⁿᶠ ⦇ n ⦈ d ↘ v ->
    Rⁿᵉ ⦇ n ⦈ (dn_app e d) ↘ (Intensional.ne_app u v)
  | rne_rec : forall n dz ds e vz vs u,
    Rⁿᶠ ⦇ n ⦈ dz ↘ vz ->
    Rⁿᶠ ⦇ n ⦈ ds ↘ vs ->
    Rⁿᵉ ⦇ n ⦈ e ↘ u ->
    Rⁿᵉ ⦇ n ⦈ (dn_rec dz ds e) ↘ (Intensional.ne_rec vs vs u)
where " 'Rⁿᶠ' ⦇ n ⦈ d ↘ v" := (RNfRel n d v) and 
      " 'Rⁿᵉ' ⦇ n ⦈ e ↘ u" := (RNeRel n e u).

Scheme rne_ind := Induction for RNeRel Sort Prop
  with rnf_ind := Induction for RNfRel Sort Prop.

Combined Scheme rne_rnf_mutind from rne_ind, rnf_ind.

Lemma rne_rnf_det : 
  ( forall n e u1, Rⁿᵉ ⦇ n ⦈ e ↘ u1 -> forall u2, Rⁿᵉ ⦇ n ⦈ e ↘ u2 -> u1 = u2 ) /\ 
  ( forall n d v1, Rⁿᶠ ⦇ n ⦈ d ↘ v1 -> forall v2, Rⁿᶠ ⦇ n ⦈ d ↘ v2 -> v1 = v2 ).
Proof.
  apply rne_rnf_mutind; intros; eauto.
  - dependent destruction H; eauto.
  - dependent destruction H1; eauto.
    apply f_equal2; eauto.
  - dependent destruction H2.
    apply f_equal3; eauto.
  - dependent destruction H0.
    eapply eval_det in e; eauto.
    subst.
    apply f_equal; eauto.
  - dependent destruction H0.
    apply f_equal; eauto.
  - dependent destruction H. auto.
  - dependent destruction H0.
    apply f_equal; eauto.
Qed.

Corollary rne_det : forall n e u1 u2, 
  Rⁿᵉ ⦇ n ⦈ e ↘ u1 -> 
  Rⁿᵉ ⦇ n ⦈ e ↘ u2 -> 
  u1 = u2.  
Proof.
  specialize rne_rnf_det. intuition. eauto.
Qed.

Corollary rnf_det : forall n d v1 v2, 
  Rⁿᶠ ⦇ n ⦈ d ↘ v1 -> 
  Rⁿᶠ ⦇ n ⦈ d ↘ v2 -> 
  v1 = v2.
Proof.
  specialize rne_rnf_det. intuition. eauto.
Qed.

Definition init_env (n : nat) : Env :=
  fun i => d_ne (dn_l (n - i - 1)).

(* Inductive SemTyping :  *)