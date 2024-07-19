Require Import Coq.Program.Equality.
Require Import nbe.systemt.syntax.

Inductive D : Set :=
  | d_zero
  | d_suc (d : D)
  | d_abs (t : Exp) (ρ : nat -> D)
  | d_neutral (dn : Dne)
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
Inductive PApp : D -> D -> D -> Prop :=
  | papp_abs : forall t ρ a b,
    ⟦ t ⟧ (ρ ↦ a) ↘ b ->
    (d_abs t ρ) ∙ a ↘ b
  | papp_app : forall e d,
    (d_neutral e) ∙ d ↘ (d_neutral (dn_app e d))
with PEval : Exp -> Env -> D -> Prop :=
  | peval_var : forall ρ n,
    ⟦ exp_var n ⟧ ρ ↘ (ρ n)
  | peval_abs : forall ρ t,
    ⟦ exp_abs t ⟧ ρ ↘ (d_abs t ρ)
  | peval_app : forall ρ r s f a b,
    ⟦ r ⟧ ρ ↘ f ->
    ⟦ s ⟧ ρ ↘ a ->
    f ∙ a ↘ b ->
    ⟦ exp_app r s ⟧ ρ ↘ b
  | peval_ze : forall ρ,
    ⟦ exp_zero ⟧ ρ ↘ d_zero
  | peval_suc : forall ρ t d,
    ⟦ t ⟧ ρ ↘ d ->
    ⟦ exp_suc t ⟧ ρ ↘ (d_suc d)
  | peval_rec : forall ρ ez es en dz ds dn a T,
    ⟦ ez ⟧ ρ ↘ dz ->
    ⟦ es ⟧ ρ ↘ ds -> 
    ⟦ en ⟧ ρ ↘ dn ->
    rec( dz , ds , dn ) ↘ a ->
    ⟦ exp_rec T ez es en ⟧ ρ ↘ a (* where does this T come from? *)
  | peval_subst : forall ρ ρ' t σ a,
    ⟦ σ ⟧s ρ ↘ ρ' ->
    ⟦ t ⟧ ρ' ↘ a ->
    ⟦ exp_subst t σ ⟧ ρ' ↘ a
with PRec : D -> D -> D -> D -> Prop :=
  | prec_ze : forall dz ds, 
    rec( dz , ds , d_zero ) ↘ dz
  | prec_suc : forall dz ds dn f a b,
    rec( dz , ds , dn) ↘ a ->
    ds ∙ dn ↘ f ->
    f ∙ a ↘ b ->
    rec( dz , ds , d_suc dn ) ↘ b
  | prec_rec : forall dz ds dn,
    rec( dz , ds , d_neutral dn) ↘ d_neutral (dn_rec dz ds dn)
with PSubst : Subst -> Env -> Env -> Prop :=
  | psubst_shift : forall ρ,
    ⟦ ↑ ⟧s ρ ↘ (drop ρ)
  | psubst_id : forall ρ,
    ⟦ es_id ⟧s ρ ↘ ρ
  | psubst_comp : forall ρ ρ' ρ'' σ1 σ2,
    ⟦ σ2 ⟧s ρ ↘ ρ' ->
    ⟦ σ1 ⟧s ρ' ↘ ρ'' ->
    ⟦ σ1 ∘ σ2 ⟧s ρ ↘ ρ''
  | psusbt_ext : forall ρ ρ' σ t a,
    ⟦ σ ⟧s ρ ↘ ρ' ->
    ⟦ t ⟧ ρ ↘ a -> (* why not ρ', but ρ *)
    ⟦ es_ext σ t ⟧s ρ ↘ (ρ ↦ a)
where "f ∙ a ↘ b" := (PApp f a b) and 
      "⟦ t ⟧ ρ ↘ a" := (PEval t ρ a) and 
      "rec( dz , ds , dn ) ↘ d" := (PRec dz ds dn d) and 
      "⟦ σ ⟧s ρ ↘ ρ'" := (PSubst σ ρ ρ').

Scheme papp_sch := Induction for PApp Sort Prop
  with peval_sch := Induction for PEval Sort Prop
  with prec_sch := Induction for PRec Sort Prop 
  with psubst_sch := Induction for PSubst Sort Prop.

Lemma papp_det : forall f a b1,
  f ∙ a ↘ b1 -> 
  forall b2,
  f ∙ a ↘ b2 -> 
  b1 = b2.
Proof.
  intros f a b1 Happ1. 
  eapply papp_sch with (P := fun f a b1 p => forall b2 : D, f ∙ a ↘ b2 -> b1 = b2)
    (P0 := fun t ρ a1 p => forall a2, ⟦ t ⟧ ρ ↘ a2 -> a1 = a2)
    (P1 := fun dz ds dn d1 p => forall d2, rec( dz , ds , dn ) ↘ d2 -> d1 = d2)
    (P2 := fun σ ρ ρ1' p => forall ρ2', ⟦ σ ⟧s ρ ↘ ρ2' -> ρ1' = ρ2')
    ; intros; auto.
  - dependent destruction H0; auto.
  - dependent destruction H. auto.
  
  - dependent destruction H. auto.
  - dependent destruction H. auto.
  - dependent destruction H2; auto.
    apply H in H2_.
    apply H0 in H2_0. subst.
    apply H1 in H2. auto.
  - dependent destruction H. auto.
  - dependent destruction H0. auto.
    apply f_equal. apply H; auto.
  - dependent destruction H3. 
    apply H in H3_.
    apply H0 in H3_0.
    apply H1 in H3_1.
    subst.
    apply H2 in H3. auto.
  - dependent destruction H1. 
    apply H0 in H2. auto.

  - dependent destruction H. auto.
  - dependent destruction H2.
    apply H0 in H3. subst.
    apply H in H2. subst.
    apply H1; auto.
  - dependent destruction H. auto.
 
  - dependent destruction H. auto.
  - dependent destruction H. auto.
  - dependent destruction H1.
    apply H in H1_. subst.
    apply H0 in H1_0. auto.
  - dependent destruction H1. apply H0 in H2. subst. auto.
Qed.

Lemma papp_det' : forall f a b1,
  f ∙ a ↘ b1 -> 
  forall b2,
  f ∙ a ↘ b2 -> 
  b1 = b2
with peval_det' : forall t ρ a1,
  ⟦ t ⟧ ρ ↘ a1 -> 
  forall a2,
  ⟦ t ⟧ ρ ↘ a2 -> 
  a1 = a2
with prec_det' : forall dz ds dn d1,
  rec( dz , ds , dn ) ↘ d1 ->
  forall d2, 
  rec( dz , ds , dn ) ↘ d2 ->
  d1 = d2
with psubst_det' : forall σ ρ ρ1',
  ⟦ σ ⟧s ρ ↘ ρ1' ->
  forall ρ2',
  ⟦ σ ⟧s ρ ↘ ρ2' ->
  ρ1' = ρ2'.
Proof.
  - clear papp_det'. intros * Happ1.
    induction Happ1; intros * Happ2; dependent destruction Happ2; auto.
    * eapply peval_det'; eauto.
  - clear peval_det'. intros * Heval1. 
    induction Heval1; intros * Heval2; dependent destruction Heval2; eauto.
    + apply IHHeval1_1 in Heval2_1; eauto.
      apply IHHeval1_2 in Heval2_2; eauto.
      subst. eapply papp_det'; eauto.
    + apply f_equal. eapply IHHeval1; eauto.
    + apply IHHeval1_1 in Heval2_1.
      apply IHHeval1_2 in Heval2_2.
      apply IHHeval1_3 in Heval2_3. subst.
      eapply prec_det'; eauto.
  - clear prec_det'. intros * Hrec1.
    induction Hrec1; intros * Hrec2; dependent destruction Hrec2; eauto.
    + apply IHHrec1 in Hrec2; subst.
      eapply papp_det' in H; eauto. subst.
      eapply papp_det' in H0; eauto.
  - clear psubst_det'. intros * Hsubst1.
    induction Hsubst1; intros * Hsubst2; dependent destruction Hsubst2; auto.
    + apply IHHsubst1_1 in Hsubst2_1. subst.
      apply IHHsubst1_2 in Hsubst2_2. auto.
    + eapply peval_det' in H; eauto. subst. auto.
Admitted.  (* cannot guess the argument of fix *)