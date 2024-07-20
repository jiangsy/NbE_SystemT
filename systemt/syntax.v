Inductive Typ : Set :=
  | typ_nat : Typ
  | typ_arr : Typ -> Typ -> Typ.

Inductive Subst : Set :=
  | es_shift 
  | es_id 
  | es_comp (σ1 σ2 : Subst)
  | es_ext (σ : Subst) (e : Exp) 
with Exp : Set :=
  | exp_var (n : nat)
  | exp_zero  
  | exp_suc (e : Exp)
  | exp_rec (T : Typ) (z s t: Exp)
  | exp_abs (e : Exp)
  | exp_app (e1 e2 : Exp)
  | exp_subst (e : Exp) (σ : Subst).

Notation "↑" := es_shift.

Notation "σ1 ∘ σ2" := (es_comp σ1 σ2) 
  (at level 49, right associativity): type_scope.
 
Definition q (σ : Subst) := es_ext (σ ∘ ↑) (exp_var 0).
  
Module Intensional.
  Inductive Ne : Set :=
  | ne_v (vi : nat)
  | ne_app (u : Ne) (v : Nf)
  | ne_rec (vz vs : Nf) (u : Ne)
  with Nf : Set :=
  | nf_ne (u : Ne)
  | nf_abs (v : Nf)
  | nf_zero
  | nf_suc (v : Nf).
End Intensional.

Module Extensional.
End Extensional.
