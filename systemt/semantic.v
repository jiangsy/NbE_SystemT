Require Import Lia.
Require Import nbe.systemt.static.

Inductive D : Prop :=
  | D_zero
  | D_suc (d : D)
  | D_abs (t : exp) (ρ : nat -> D)
  | D_neutral (dn : Dn)
with Dn : Prop :=
  | Dn_l (n : nat) 
  | Dn_rec (z s : D) (dn : Dn)
  | Dn_app (dn : Dn) (d : D).