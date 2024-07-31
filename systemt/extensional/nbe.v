Require Import nbe.systemt.extensional.syntax.
Require Import nbe.systemt.extensional.semantic.

Definition Nbe (n : nat) (ρ : Env) (t : Exp) (T: Typ) (w : Nf) :=
  exists a, ⟦ t ⟧ ρ ↘ a /\ Rⁿᶠ ⦇ n ⦈ (dnf_reif T a) ↘ w.

Definition Completenss' (n : nat) (ρ ρ' : Env) (s t : Exp) (T : Typ) :=
  exists w, Nbe n ρ s T w /\ Nbe n ρ' t T w.

Definition Completenss (n : nat) (ρ : Env) (s t : Exp) (T : Typ) :=
  exists w, Nbe n ρ s T w /\ Nbe n ρ t T w.

Definition Soundness (Γ : Ctx) (t : Exp) (T : Typ) (ρ : Env) : Prop :=
  exists w, Nbe (length Γ) ρ t T w /\ Γ ⊢ t ≈ w : T.
