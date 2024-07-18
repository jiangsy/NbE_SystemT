Require Import Lia.
Require Import nbe.systemt.static.

Inductive D : Prop :=
  | d_zero
  | d_suc (d : D)
  | d_abs (t : Exp) (ρ : nat -> D)
  | d_neutral (dn : Dne)
with Dne : Prop :=
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

Reserved Notation "f ∙ a ↘ b "
  (at level 55, a at next level, no associativity).
Reserved Notation "⟦ t ⟧ ρ ↘ a "
  (at level 55, ρ at next level, no associativity).
Reserved Notation "rec( dz , ds , dn ) ↘ d "
  (at level 55, ds at next level, dn at next level, no associativity).
Reserved Notation "⟦ σ ⟧s ρ ↘ ρ' "
  (at level 55, ρ at next level, no associativity).
Inductive PApp : D -> D -> D -> Prop :=
  | papp_abs : forall t ρ a b,
      PEval t (ρ ↦ a) b ->
      (d_abs t ρ) ∙ a ↘ b
  | papp_app : forall e d,
      (d_neutral e) ∙ d ↘ (d_neutral (dn_app e d))
with PEval : Exp -> Env -> D -> Prop :=
  | peval_ze : forall ρ,
     ⟦ exp_zero ⟧ ρ ↘ d_zero
with PRec : D -> D -> D -> D -> Prop :=
  | prec_ze : forall dz dn, 
     rec( dz , dn , d_zero ) ↘ dz
with PSubst : Subst -> Env -> Env -> Prop :=
  | psubst_shift : forall ρ,
     ⟦ ↑ ⟧s ρ ↘ (drop ρ)
where  "f ∙ a ↘ b " := (PApp f a b) and 
       "⟦ t ⟧ ρ ↘ a" := (PEval t ρ a) and 
       "rec( dz , ds , dn ) ↘ d " := (PRec dz ds dn d) and 
       "⟦ σ ⟧s ρ ↘ ρ' " := (PSubst σ ρ ρ').
