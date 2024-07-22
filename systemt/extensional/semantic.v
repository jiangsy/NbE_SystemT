Require Import Coq.Program.Equality.
Require Import nbe.systemt.extensional.syntax.

Inductive D : Set :=
  | d_zero
  | d_suc (d : D)
  | d_abs (t : Exp) (ρ : nat -> D)
  | d_refl (T: Typ) (e : Dne)
with Dne : Set :=
  | dne_l (n : nat) 
  | dne_rec (dz ds : Dnf) (dn : Dne)
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
    ⟦ exp_subst t σ ⟧ ρ' ↘ a
with RecRel : Typ -> D -> D -> D -> D -> Prop :=
  | rec_ze : forall az aₛ T, 
    rec( T , az , aₛ , d_zero ) ↘ az
  | rec_suc : forall az aₛ an f a b T,
    rec( T , az , aₛ , an) ↘ a ->
    aₛ ∙ an ↘ f ->
    f ∙ a ↘ b ->
    rec( T , az , aₛ , d_suc an ) ↘ b
  | rec_rec : forall az aₛ e T,
    rec( T , az , aₛ , d_refl ℕ e) ↘ d_refl T (dne_rec (dnf_reif T az) (dnf_reif (ℕ → T → T) aₛ) e)
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
  apply app_eval_rec_subst_mutind; intros.
Admitted.

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
