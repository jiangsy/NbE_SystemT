Require Import Coq.Program.Equality.
Require Import nbe.systemt.extensional.syntax.

Inductive D : Set :=
  | d_zero
  | d_suc (d : D)
  | d_abs (t : Exp) (ρ : nat -> D)
  | d_refl (T: Typ) (e : Dne)
with Dne : Set :=
  | dne_l (n : nat) 
  | dne_rec (T : Typ) (dz ds : Dnf) (dn : Dne)
  | dne_app (e : Dne) (d : Dnf)
with Dnf : Set :=
  | dnf_reif (T : Typ) (a : D).

Notation " ( 'ƛ' t ) ρ " := (d_abs t ρ)
  (at level 55).

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
Reserved Notation "rec( T , dz , ds , dn ) ↘ d"
  (at level 55, dz at next level, ds at next level, dn at next level, no associativity).
Reserved Notation "⟦ σ ⟧s ρ ↘ ρ'"
  (at level 55, ρ at next level, no associativity).
Inductive AppRel : D -> D -> D -> Prop :=
  | app_abs : forall t ρ a b,
    ⟦ t ⟧ (ρ ↦ a) ↘ b ->
    (d_abs t ρ) ∙ a ↘ b
  | app_app : forall e d S T,
    (d_refl (S → T) e) ∙ d ↘ (d_refl T (dne_app e (dnf_reif T d)))
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
    rec( T , dz , ds , dn ) ↘ a ->
    ⟦ exp_rec T ez es en ⟧ ρ ↘ a 
  | eval_subst : forall ρ ρ' t σ a,
    ⟦ σ ⟧s ρ ↘ ρ' ->
    ⟦ t ⟧ ρ' ↘ a ->
    ⟦ exp_subst t σ ⟧ ρ ↘ a
with RecRel : Typ -> D -> D -> D -> D -> Prop :=
  | rec_ze : forall az aₛ T, 
    rec( T , az , aₛ , d_zero ) ↘ az
  | rec_suc : forall az aₛ an f a b T,
    rec( T , az , aₛ , an) ↘ a ->
    aₛ ∙ an ↘ f ->
    f ∙ a ↘ b ->
    rec( T , az , aₛ , d_suc an ) ↘ b
  | rec_rec : forall az aₛ e T,
    rec( T , az , aₛ , d_refl ℕ e) ↘ d_refl T (dne_rec T (dnf_reif T az) (dnf_reif (ℕ → T → T) aₛ) e)
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
      "rec( T , dz , ds , dn ) ↘ d" := (RecRel T dz ds dn d) and 
      "⟦ σ ⟧s ρ ↘ ρ'" := (SubstRel σ ρ ρ').


Scheme app_ind := Induction for AppRel Sort Prop
  with eval_ind := Induction for EvalRel Sort Prop
  with rec_ind := Induction for RecRel Sort Prop 
  with subst_ind := Induction for SubstRel Sort Prop.

Combined Scheme app_eval_rec_subst_mutind from app_ind, eval_ind, rec_ind, subst_ind.

Lemma app_eval_rec_subst_det : 
  ( forall f a b1, f ∙ a ↘ b1 -> forall b2, f ∙ a ↘ b2 ->  b1 = b2 ) /\
  ( forall t ρ a1, ⟦ t ⟧ ρ ↘ a1 -> forall a2, ⟦ t ⟧ ρ ↘ a2 -> a1 = a2 ) /\
  ( forall T az aₛ an d1, rec( T , az , aₛ , an ) ↘ d1 -> forall d2,  rec( T , az , aₛ , an ) ↘ d2 -> d1 = d2 ) /\
  ( forall σ ρ ρ1', ⟦ σ ⟧s ρ ↘ ρ1' -> forall ρ2', ⟦ σ ⟧s ρ ↘ ρ2' -> ρ1' = ρ2' ).
Proof.
  apply app_eval_rec_subst_mutind; intros; 
    try solve [dependent destruction H; eauto; try apply f_equal; try apply f_equal2; eauto];
    try solve [dependent destruction H0; eauto;  try apply f_equal; try apply f_equal2; eauto].
  - dependent destruction H2. 
    apply H in H2_.
    apply H0 in H2_0. subst.
    apply H1 in H2; eauto.
  - dependent destruction H3; eauto.
    apply H in H3_.
    apply H0 in H3_0. 
    apply H1 in H3_1. subst.
    eauto.
  - dependent destruction H1.
    apply H in H1. subst.
    apply H0 in H2; eauto.
  - dependent destruction H2.
    apply H0 in H3. subst.
    apply H in H2. subst. eauto.
  - dependent destruction H1.
    apply H in H1_. subst. eauto.
  - dependent destruction H1.
    apply H in H1. subst. apply f_equal2; eauto.
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

Theorem rec_det : forall T az aₛ an a1 a2, 
  rec( T , az , aₛ , an ) ↘ a1 -> 
  rec( T , az , aₛ , an ) ↘ a2 -> 
  a1 = a2.
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
Inductive RNfRel : nat -> Dnf -> Nf -> Prop := 
  | rnf_abs : forall f b n t S T,
    f ∙ (d_refl S (dne_l n)) ↘ b ->
    Rⁿᶠ ⦇ 1 + n ⦈ (dnf_reif T b) ↘ t ->
    Rⁿᶠ ⦇ n ⦈ (dnf_reif (S → T) f) ↘ (nf_abs t)
  | rnf_zero : forall n,
    Rⁿᶠ ⦇ n ⦈ (dnf_reif ℕ d_zero) ↘ nf_zero
  | rnf_suc : forall n a t,
    Rⁿᶠ ⦇ n ⦈ (dnf_reif ℕ a) ↘ t ->
    Rⁿᶠ ⦇ n ⦈ (dnf_reif ℕ (d_suc a)) ↘ (nf_suc t)
  | rnf_ne : forall n e t,
    Rⁿᵉ ⦇ n ⦈ e ↘ t ->
    Rⁿᶠ ⦇ n ⦈ (dnf_reif ℕ (d_refl ℕ e)) ↘ (nf_ne t)
with RNeRel : nat -> Dne -> Ne -> Prop :=
  | rne_v : forall n k,
    Rⁿᵉ ⦇ n ⦈ (dne_l k) ↘ (ne_v (n - k - 1))
  | rne_app : forall n e d u v,
    Rⁿᵉ ⦇ n ⦈ e ↘ u ->
    Rⁿᶠ ⦇ n ⦈ d ↘ v ->
    Rⁿᵉ ⦇ n ⦈ (dne_app e d) ↘ (ne_app u v)
  | rne_rec : forall n dz ds e vz vs u T,
    Rⁿᶠ ⦇ n ⦈ dz ↘ vz ->
    Rⁿᶠ ⦇ n ⦈ ds ↘ vs ->
    Rⁿᵉ ⦇ n ⦈ e ↘ u ->
    Rⁿᵉ ⦇ n ⦈ (dne_rec T dz ds e) ↘ (ne_rec T vs vs u)
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
    eapply app_det in a; eauto. subst.
    apply H in H1. subst. auto.
  - dependent destruction H. auto.
  - dependent destruction H0.
    apply H in H0. 
    apply f_equal; eauto.
  - dependent destruction H0.
    apply H in H0.
    apply f_equal; auto.
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
