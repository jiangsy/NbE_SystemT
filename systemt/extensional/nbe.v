Require Import nbe.systemt.extensional.syntax.
Require Import nbe.systemt.extensional.semantic.

Definition Nbe (n : nat) (ρ : Env) (t : Exp) (T: Typ) (w : Nf) :=
  exists a, ⟦ t ⟧ ρ ↘ a /\ Rⁿᶠ ⦇ n ⦈ (dnf_reif T a) ↘ w.

Definition Completenss' (n : nat) (ρ ρ' : Env) (s t : Exp) (T : Typ) :=
  exists w, Nbe n ρ s T w /\ Nbe n ρ' t T w.

Definition Completenss (n : nat) (ρ : Env) (s t : Exp) (T : Typ) :=
  exists w, Nbe n ρ s T w /\ Nbe n ρ t T w.
