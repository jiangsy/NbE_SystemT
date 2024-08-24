Require Import nbe.ptt.syntax.def.

Reserved Notation "'Env'".
Inductive D : Set :=
| d_nat
| d_set (i : nat)
| d_pi (a : D) (t : Exp) (ρ : Env)
| d_zero
| d_suc (a : D)
| d_abs (t : Exp) (ρ : Env) 
| d_refl (a : D) (e : Dne)
with Dnf : Set :=
| d_reif (e : Dne) (d : Dnf)
with Dne : Set :=
| dne_var (n : nat)
| dne_rec (T : Typ) (a : D) (t : Exp) (ρ : Env) (e : Dne)
| dne_app (e : Dne) (d : Dnf)
where "'Env'" := (nat -> D).