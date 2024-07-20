Require Import Coq.Lists.List.

Inductive Typ : Set :=
  | typ_nat : Typ
  | typ_arr : Typ -> Typ -> Typ.

Notation "S → T" := (typ_arr S T)
  (at level 54, right associativity).

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

Notation "'ℕ'" := typ_nat.

Notation "↑" := es_shift.

Notation "σ1 ∘ σ2" := (es_comp σ1 σ2) 
  (at level 49, right associativity): type_scope.
 
Definition q (σ : Subst) := es_ext (σ ∘ ↑) (exp_var 0).

Definition Ctx := list Typ.
  
Reserved Notation "Γ ⊢ t : T" 
  (at level 55, t at next level, no associativity).
Reserved Notation "Γ ⊢s σ : Δ"
  (at level 55, σ at next level, no associativity).
Inductive Typing : Ctx -> Exp -> Typ -> Prop := 
  | typing_v : forall Γ i T,
    nth_error Γ i = Some T ->
    Γ ⊢ (exp_var i) : T
  | typing_abs : forall Γ S T t ,
    (S :: Γ) ⊢ t : T ->
    Γ ⊢ (exp_abs t) : S → T
  | typing_app : forall Γ r s S T,
    Γ ⊢ r : S → T ->
    Γ ⊢ s : S ->
    Γ ⊢ (exp_app r s) : T
  | typing_zero : forall Γ,
    Γ ⊢ exp_zero : ℕ
  | typing_suc : forall Γ t,
    Γ ⊢ t : ℕ ->
    Γ ⊢ (exp_suc t) : ℕ
  | typing_rec : forall Γ tz ts tn T,
    Γ ⊢ tz : T ->
    Γ ⊢ ts : ℕ → T → T ->
    Γ ⊢ tn : ℕ ->
    Γ ⊢ exp_rec T tz ts tn : T
  | typing_subst : forall Γ Δ t σ T,
    Γ ⊢s σ : Δ ->
    Δ ⊢ t : T ->
    Γ ⊢ (exp_subst t σ) : T
with  SubstTyping : Ctx -> Subst -> Ctx -> Prop := 
  | styping_shift : forall S Γ,
    (S :: Γ) ⊢s ↑ : Γ
  | styping_id : forall Γ,
    Γ ⊢s es_id : Γ
  | styping_comp : forall Γ1 Γ2 Γ3 σ τ,
    Γ1 ⊢s τ : Γ2 ->
    Γ2 ⊢s σ : Γ3 ->
    Γ1 ⊢s (σ ∘ τ) : Γ3
  | styping_exp : forall Γ Δ σ s S,
    Γ ⊢s σ : Δ ->
    Γ ⊢ s : S ->
    Γ ⊢s (es_ext σ s) : (S :: Δ)
where "Γ ⊢ t : T" := (Typing Γ t T) and
      "Γ ⊢s σ : Δ" := (SubstTyping Γ σ Δ).

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
  Inductive Ne : Set :=
  | ne_v (vi : nat)
  | ne_app (u : Ne) (v : Nf)
  | ne_rec (T : Typ) (vz vs : Nf) (u : Ne)
  with Nf : Set :=
  | nf_ne (u : Ne)
  | nf_abs (v : Nf)
  | nf_zero
  | nf_suc (v : Nf).
End Extensional.
