Require Import nbe.systemt.intensional.syntax.
Require Import nbe.systemt.intensional.semantic.

Definition init_env (n : nat) : Env :=
  fun i => d_ne (dn_l (n - i - 1)).

Definition nbe (n : nat) (t : Exp) (w : Nf) : Prop := 
  exists d, ⟦ t ⟧ (init_env n) ↘ d /\ Rⁿᶠ ⦇ n ⦈ d ↘ w.