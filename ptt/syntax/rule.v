Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.

Require Import nbe.ptt.syntax.def.

Definition subst0 : Exp -> Exp -> Exp :=
  fun t s => t [ subst_ext subst_id s ].

Reserved Notation "⊢ Γ"
  (at level 55, no associativity).
Reserved Notation "Γ ⊢ t : T"
  (at level 55, t at next level, no associativity).
Reserved Notation "Γ ⊢s σ : Δ"
  (at level 55, σ at next level, no associativity).
Reserved Notation  "Γ ⊢ t ≈ t' : T" 
  (at level 55, t at next level, t' at next level, no associativity).
Reserved Notation  "Γ ⊢s σ ≈ σ' : Δ" 
  (at level 55, σ at next level, σ' at next level, no associativity).
Inductive WfCtx : Ctx -> Prop :=
| wf_ctx_nil : ⊢ nil
| wf_ctx_cons : forall Γ T i,
  ⊢ Γ ->
  Γ ⊢ T : (exp_set i) ->
  ⊢ (T :: Γ)
with Typing : Ctx -> Exp -> Exp -> Prop :=
| typing_nat : forall Γ i,
  ⊢ Γ ->
  Γ ⊢ exp_nat : (exp_set i)
| typing_set : forall Γ i,
  ⊢ Γ ->
  Γ ⊢ (exp_set i) : (exp_set (1 + i))
| typing_pi : forall Γ S T i,
  Γ ⊢ S : exp_set i ->
  (S :: Γ) ⊢ T : exp_set i ->
  Γ ⊢ exp_pi S T : exp_set i
| typing_var : forall Γ n T,
  InCtx n T Γ ->
  Γ ⊢ (exp_var n) : T
| typing_zero : forall Γ,
  Γ ⊢ exp_zero : exp_nat
| typing_suc : forall Γ t,
  Γ ⊢ t : exp_nat ->
  Γ ⊢ (exp_suc t) : exp_nat
| typing_rec : forall Γ tz ts tn T i,
  (ℕ :: Γ) ⊢ T : exp_set i ->
  Γ ⊢ tz : subst0 T exp_zero ->
  (T :: ℕ :: Γ) ⊢ ts : ( T [ subst_ext (↑ ∘ ↑) (exp_suc (exp_var 1)) ] ) ->
  Γ ⊢ exp_rec T tz ts tn : subst0 T tn
| typing_abs : forall Γ t S T i,
  Γ ⊢ S : exp_set i ->
  (S :: Γ) ⊢ t : T ->
  Γ ⊢ (exp_abs t) : (exp_pi S T) 
| typing_app : forall Γ r s S T i,
  Γ ⊢ S : exp_set i ->
  (S :: Γ) ⊢ T : exp_set i ->
  Γ ⊢ r : exp_pi S T ->
  Γ ⊢ s : S ->
  Γ ⊢ r ▫ s : subst0 T s
| typing_subst : forall Γ Δ σ t T,
  Γ ⊢s σ : Δ ->
  Γ ⊢ t : T ->
  Γ ⊢ t [ σ ] : T [ σ ]
| typing_cumu : forall Γ T i,
  Γ ⊢ T : exp_set i ->
  Γ ⊢ T : exp_set (1 + i)
| typing_conv : forall Γ t S T i,
  Γ ⊢ t : T ->
  Γ ⊢ T ≈ S : exp_set i ->
  Γ ⊢ t : S
with SubstTyping : Ctx -> Subst -> Ctx -> Prop :=
| subst_typing_id : forall Γ,
  Γ ⊢s subst_id : Γ
| subst_typing_shift : forall Γ T,
  (T :: Γ) ⊢s ↑ : Γ
| subst_typing_comp : forall Γ1 Γ2 Γ3 σ1 σ2,
  Γ1 ⊢s σ1 : Γ2 ->
  Γ2 ⊢s σ2 : Γ3 ->
  Γ1 ⊢s σ2 ∘ σ1 : Γ3
| subst_typing_ext : forall Γ Δ σ t T i,
  Γ ⊢s σ : Δ ->
  Δ ⊢ T : exp_set i ->
  Γ ⊢ t : T [ σ ] ->
  Γ ⊢s subst_ext σ t : (T :: Δ)
| subst_typing_conv : forall Γ Δ σ σ',
  Γ ⊢s σ : Δ ->
  Γ ⊢s σ ≈ σ' : Δ ->
  Γ ⊢s σ' : Δ
with EqExp : Ctx -> Exp -> Exp -> Exp -> Prop :=
| eq_exp_prop_nat : forall Γ Δ σ i,
  Γ ⊢s σ : Δ ->
  Γ ⊢ ℕ [ σ ] ≈ ℕ : exp_set i
| eq_exp_prop_set : forall Γ Δ σ i,
  Γ ⊢s σ : Δ ->
  Γ ⊢ exp_set i [ σ ] ≈ exp_set i : exp_set (1 + i)
| eq_exp_prop_pi : forall Γ Δ σ S T i,
  Γ ⊢s σ : Δ ->
  Γ ⊢ S : exp_set i ->
  (S :: Γ) ⊢ T : exp_set i ->
  Γ ⊢ exp_pi S T [ σ ] ≈ exp_pi (S [ σ ]) (T [subst_ext (σ ∘ ↑) (exp_var 0)]) : exp_set i
| eq_exp_prop_zero : forall Γ Δ σ,
  Γ ⊢s σ : Δ ->
  Γ ⊢ exp_zero ≈ exp_zero [ σ ] : ℕ
| eq_exp_prop_suc : forall Γ Δ t σ,
  Γ ⊢s σ : Δ ->
  Δ ⊢ t : ℕ ->
  Γ ⊢ exp_suc t [ σ ] ≈ exp_suc (t [ σ ]) : ℕ
| eq_exp_prop_app : forall Γ Δ r s σ S T,
  Γ ⊢s σ : Δ ->
  Δ ⊢ r : exp_pi S T ->
  Δ ⊢ s : S ->
  Γ ⊢ (r ▫ s) [ σ ] ≈ (r [ σ ]) ▫ (s [ σ ]) : T [ subst_ext σ (s [ σ ]) ]
| eq_exp_prop_rec : forall Γ Δ σ tz ts tn T i,
  Γ ⊢s σ : Δ ->
  (ℕ :: Δ) ⊢ T : exp_set i ->
  Δ ⊢ tz : subst0 T exp_zero ->
  (T :: ℕ :: Γ) ⊢ ts : T [ subst_ext ( ↑ ∘ ↑ ) (exp_var 1) ] ->
  Δ ⊢ tn : ℕ ->
  Γ ⊢ exp_rec T tz ts tn [ σ ] ≈ exp_rec T tz ts tn [ σ ] : T
| eq_exp_prop_abs : forall Γ Δ σ t S T,
  Γ ⊢s σ : Δ ->
  Γ ⊢ (λ t) [ σ ] ≈ (λ (t [subst_ext (σ ∘ subst_shift) (exp_var 0)])) : (exp_pi S T) [ σ ]
| eq_exp_comp_pi : forall Γ S S' T T' i, 
  Γ ⊢ S : exp_set i ->
  Γ ⊢ S ≈ S' : exp_set i ->
  (S :: Γ) ⊢ T ≈ T' : exp_set i ->
  Γ ⊢ exp_pi S T ≈ exp_pi S' T' : exp_set i
| eq_exp_comp_var : forall Γ i T,
  InCtx i T Γ ->
  Γ ⊢ exp_var i ≈ exp_var i : T
| eq_exp_comp_suc : forall Γ t t',
  Γ ⊢ t ≈ t' : ℕ ->
  Γ ⊢ exp_suc t ≈ exp_suc t' : ℕ
| eq_exp_comp_app : forall Γ r r' s s' S T i,
  Γ ⊢ S : exp_set i ->
  (S :: Γ) ⊢ T : exp_set i ->
  Γ ⊢ r ≈ r' : exp_pi S T ->
  Γ ⊢ s ≈ s' : S ->
  Γ ⊢ r ▫ s ≈ r' ▫ s' : subst0 T s
| eq_exp_comp_rec : forall Γ tz tz' ts ts' tn tn' T T' i,
  (ℕ :: Γ) ⊢ T : exp_set i ->
  Γ ⊢ tz ≈ tz' : subst0 T exp_zero ->
  (T :: ℕ :: Γ) ⊢ ts : T [ subst_ext (↑ ∘ ↑) (exp_suc (exp_var 1)) ] ->
  Γ ⊢ tn ≈ tn' : ℕ ->
  Γ ⊢ T ≈ T' : exp_set i ->
  Γ ⊢ exp_rec T tz ts tn ≈ exp_rec T' tz' ts' tn' : T
| eq_exp_comp_abs : forall Γ t t' S T i,
  Γ ⊢ S : exp_set i ->
  (S :: Γ) ⊢ t ≈ t' : T ->
  Γ ⊢ (λ t) ≈ (λ t') : exp_pi S T
| eq_exp_comp_subst : forall Γ Δ t t' σ σ' T,
  Γ ⊢s σ ≈ σ' : Δ ->
  Δ ⊢ t ≈ t' : T ->
  Γ ⊢ t [ σ ] ≈ t' [ σ' ] : T
| eq_exp_beta_abs : forall Γ t s S T i,
  Γ ⊢ S : exp_set i ->
  (S :: Γ) ⊢ T : exp_set i ->
  (S :: Γ) ⊢ t : T ->
  Γ ⊢ s : S ->
  Γ ⊢ (λ t) ▫ s ≈ subst0 t s : subst0 T s 
| eq_exp_beta_rec_zero : forall Γ tz ts T i,
  (ℕ :: Γ) ⊢ T : exp_set i ->
  (* why dont check ts? *)
  Γ ⊢ tz : subst0 T exp_zero ->
  Γ ⊢ exp_rec T tz ts exp_zero ≈ tz : subst0 T exp_zero
| eq_exp_beta_rec_suc : forall Γ tz ts tn T i,
  (ℕ :: Γ) ⊢ T : exp_set i ->
  Γ ⊢ tz : subst0 T exp_zero ->
  (T :: ℕ :: Γ) ⊢ ts : T [ subst_ext (↑ ∘ ↑) (exp_suc (exp_var 1)) ] ->
  Γ ⊢ tn : ℕ ->
  (* Γ ⊢ exp_rec T tz ts (exp_suc tn) ≈ ts [ subst_ext (subst_ext subst_id tn) (exp_rec T tz ts tn) ] : subst0 T (exp_suc tn) *)
  Γ ⊢ exp_rec T tz ts (exp_suc tn) ≈ ts ▫ tn ▫ exp_rec T tz ts tn : subst0 T (exp_suc tn)
| eq_exp_eta_abs : forall Γ t S T i,
  Γ ⊢ S : exp_set i ->
  (S :: Γ) ⊢ T : exp_set i ->
  Γ ⊢ t : exp_pi S T ->
  Γ ⊢ t ≈ exp_abs (t [ ↑ ] ▫ (exp_var 0)) : exp_pi S T
| eq_exp_subst_id : forall Γ t T,
  Γ ⊢ t : T ->
  Γ ⊢ t [ subst_id ] ≈ t : T
| eq_exp_substs_shift : forall Γ S T i,
  InCtx i T Γ ->
  ⊢ (S :: Γ) ->
  (S :: Γ) ⊢ exp_var i [ ↑ ] ≈ exp_var (1 + i) : T [ ↑ ]
| eq_exp_subst_comp : forall Γ1 Γ2 Γ3 σ1 σ2 t T,
  Γ1 ⊢s σ1 : Γ2 ->
  Γ2 ⊢s σ2 : Γ3 ->
  Γ3 ⊢ t : T ->
  Γ1 ⊢ t [ σ2 ∘ σ1 ] ≈ t [ σ2 ] [ σ1 ] : T [ σ2 ∘ σ1 ]
| eq_exp_subst_ext_var_0 : forall Γ Δ σ s S i,
  Γ ⊢s σ : Δ ->
  Δ ⊢ S : exp_set i ->
  Γ ⊢ s : S [ σ ] ->
  Γ ⊢ exp_var 0 [ subst_ext σ s ] ≈ s : S [ σ ] 
| eq_exp_subst_ext_var_sn : forall Γ Δ σ s S T n i,
  Γ ⊢s σ : Δ ->
  Δ ⊢ S : exp_set i ->
  Γ ⊢ s : S [ σ ] ->
  InCtx n T Δ ->
  Γ ⊢ exp_var (1 + n) [ subst_ext σ s ] ≈ exp_var n [ σ ] : T [ σ ]
| eq_exp_conv : forall Γ t t' T T' i,
  Γ ⊢ t ≈ t' : T ->
  Γ ⊢ T ≈ T' : exp_set i ->
  Γ ⊢ t ≈ t' : T'
| eq_exp_cumu : forall Γ T T' i,
  Γ ⊢ T ≈ T' : exp_set i ->
  Γ ⊢ T ≈ T' : exp_set (1 + i)
| eq_exp_sym : forall Γ t t' T,
  Γ ⊢ t ≈ t' : T ->
  Γ ⊢ t' ≈ t : T
| eq_exp_trans : forall Γ t1 t2 t3 T,
  Γ ⊢ t1 ≈ t2 : T ->
  Γ ⊢ t2 ≈ t3 : T ->
  Γ ⊢ t1 ≈ t3 : T
with EqSubst : Ctx -> Subst -> Subst -> Ctx -> Prop :=
where "⊢ Γ" := (WfCtx Γ) and
      "Γ ⊢ t : T" := (Typing Γ t T) and 
      "Γ ⊢s σ : Δ" := (SubstTyping Γ σ Δ) and 
      "Γ ⊢ t ≈ t' : T" := (EqExp Γ t t' T) and 
      "Γ ⊢s σ ≈ σ' : Δ" := (EqSubst Γ σ σ' Δ).