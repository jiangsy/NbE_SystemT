Require Import Lia.
Require Import nbe.systemt.static.

Inductive D : Prop :=
  | d_zero
  | d_suc (d : D)
  | d_abs (t : Exp) (ρ : nat -> D)
  | d_neutral (dn : Dn)
with Dn : Prop :=
  | dn_l (n : nat) 
  | dn_rec (z s : D) (dn : Dn)
  | dn_app (dn : Dn) (d : D).

Definition Env := nat -> D.

Definition add (ρ : Env) (d : D) (n : nat) : D :=
  match n with 
  | 0 => d
  | S n => ρ n
  end.

Definition drop : Env -> Env :=
  fun ρ n => ρ (S n).

Inductive PApp : D -> D -> D -> Prop :=
  | papp_abs : forall t ρ a b,
      PEval t (add ρ a) b ->
      PApp (d_abs t ρ) a b
with PEval : Exp -> Env -> D -> Prop :=
  | peval_ze : forall ρ,
      PEval exp_zero ρ d_zero
with PRec : D -> D -> D -> D -> Prop :=
  | prec_ze : forall d1 d2, 
      PRec d1 d2 d_zero d1
with PSubst : Subst -> Env -> Env -> Prop :=
  | psubst_shift : forall ρ,
     PSubst ↑ ρ (drop ρ).