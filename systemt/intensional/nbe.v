Require Import nbe.systemt.syntax.
Require Import nbe.systemt.semantic.

Definition init_env (n : nat) : Env :=
  fun i => d_ne (dn_l (n - i - 1)).

Definition nbe (n : nat) (t : Exp) (w : Intensional.Nf) : Prop := 
  exists d, ⟦ t ⟧ (init_env n) ↘ d /\ Rⁿᶠ ⦇ n ⦈ d ↘ w.