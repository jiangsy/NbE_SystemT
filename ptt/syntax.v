Require Import Coq.Lists.List.

Inductive Subst : Set :=
| subst_shift 
| susbt_id 
| subst_comp (σ1 σ2 : Subst)
| subst_ext (σ : Subst) (e : Exp) 
with Exp : Set :=
| exp_var (n : nat)
| exp_zero  
| exp_suc (e : Exp)
| exp_rec (V : Exp) (z s n: Exp)
| exp_abs (e : Exp)
| exp_app (e1 e2 : Exp)
| exp_subst (e : Exp) (σ : Subst)
| exp_nat
| exp_set (k : nat)
| exp_fun (S T : Exp).

Definition Ctx := list Exp.

Notation "'ℕ'" := exp_nat.

Notation "↑" := subst_shift.

Notation "'λ' t" := (exp_abs t)
  (at level 55). 

Notation " t [ σ ] " := (exp_subst t σ)
  (at level 52, left associativity).

Notation "r ▫ s" := (exp_app r s)
  (at level 53, left associativity).

Notation "σ1 ∘ σ2" := (subst_comp σ1 σ2) 
  (at level 49, right associativity): type_scope.

Notation "S → T" := (exp_fun S (exp_abs (exp_subst T subst_shift)))
  (at level 55, right associativity).

Inductive Nf : Set :=
| nf_ne (u : Ne)
| nf_zero 
| nf_suc (v : Nf)
| nf_abs (v : Nf)
| nf_nat
| nf_fun (V W : Nf)
| nf_set (k : nat)
with Ne : Set :=
| ne_var (i : nat)
| ne_app (u : Ne) (v : Nf)
| ne_rec (V : Nf) (vz vs : Nf) (u : Ne).

Fixpoint nf_to_exp (v : Nf) : Exp :=
  match v with
  | nf_ne u => ne_to_exp u
  | nf_zero => exp_zero
  | nf_suc v => exp_suc (nf_to_exp v)
  | nf_abs v => exp_abs (nf_to_exp v)
  | nf_nat => exp_nat
  | nf_fun V W => exp_fun (nf_to_exp V) (nf_to_exp W)
  | nf_set k => exp_set k
  end
with ne_to_exp (u : Ne) : Exp :=
  match u with 
  | ne_var i => exp_var i
  | ne_app u v => exp_app (ne_to_exp u) (nf_to_exp v)
  | ne_rec V vz vs u => exp_rec (nf_to_exp V) (nf_to_exp vz) (nf_to_exp vs) (ne_to_exp u)
  end.

Coercion nf_to_exp : Nf >-> Exp.
Coercion ne_to_exp : Ne >-> Exp.

Inductive InCtx : nat -> Exp -> Ctx -> Prop :=
| in_here : forall T Γ, 
  InCtx 0 (T [ ↑ ]) (T :: Γ)
| in_there : forall n S T Γ,
  InCtx n T Γ ->
  InCtx (1 + n) (T [ ↑ ]) (S :: Γ).