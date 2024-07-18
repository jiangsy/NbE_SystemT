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