Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.
Require Import Lia.

Require Import nbe.ptt.syntax.def.

Definition subst0 : Exp -> Exp -> Exp :=
  fun t s => t [ subst_ext subst_id s ].

Notation "t [| s ]" := (subst0 t s)
  (at level 54, left associativity).

Reserved Notation "⊢ Γ"
  (at level 55, Γ at next level, no associativity).
Reserved Notation "⊢ Γ ≈ Γ'"
  (at level 55, Γ at next level, no associativity).
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
  Γ ⊢ T : (𝕊 i) ->
  ⊢ (T :: Γ)
with EqCtx : Ctx -> Ctx -> Prop :=
| eq_ctx_nil : ⊢ nil ≈ nil
| eq_ctx_cons : forall Γ Γ' T T' i,
  ⊢ Γ ≈ Γ' ->
  Γ ⊢ T : 𝕊 i ->
  Γ' ⊢ T' : 𝕊 i ->
  Γ ⊢ T ≈ T' : 𝕊 i ->
  Γ' ⊢ T ≈ T' : 𝕊 i ->
  ⊢ (T :: Γ) ≈ (T' :: Γ')
with Typing : Ctx -> Exp -> Exp -> Prop :=
| typing_nat : forall Γ i,
  ⊢ Γ ->
  Γ ⊢ exp_nat : (𝕊 i)
| typing_set : forall Γ i,
  ⊢ Γ ->
  Γ ⊢ (𝕊 i) : (exp_set (1 + i))
| typing_pi : forall Γ S T i,
  Γ ⊢ S : 𝕊 i ->
  (S :: Γ) ⊢ T : 𝕊 i ->
  Γ ⊢ exp_pi S T : 𝕊 i
| typing_var : forall Γ n T,
  ⊢ Γ ->
  n : T ∈ Γ ->
  Γ ⊢ (exp_var n) : T
| typing_zero : forall Γ,
  ⊢ Γ ->
  Γ ⊢ exp_zero : exp_nat
| typing_suc : forall Γ t,
  Γ ⊢ t : exp_nat ->
  Γ ⊢ (exp_suc t) : exp_nat
| typing_rec : forall Γ tz ts tn T i,
  (ℕ :: Γ) ⊢ T : 𝕊 i ->
  Γ ⊢ tz : T [| exp_zero ] ->
  (T :: ℕ :: Γ) ⊢ ts : ( T [ subst_ext (↑ ∘ ↑) (exp_suc (exp_var 1)) ] ) ->
  Γ ⊢ tn : ℕ ->
  Γ ⊢ exp_rec T tz ts tn : T [| tn ]
| typing_abs : forall Γ t S T i,
  Γ ⊢ S : 𝕊 i ->
  (S :: Γ) ⊢ t : T ->
  Γ ⊢ (exp_abs t) : (exp_pi S T) 
| typing_app : forall Γ r s S T i,
  Γ ⊢ S : 𝕊 i ->
  (S :: Γ) ⊢ T : 𝕊 i ->
  Γ ⊢ r : exp_pi S T ->
  Γ ⊢ s : S ->
  Γ ⊢ r ▫ s : T [| s ]
| typing_subst : forall Γ Δ σ t T,
  Γ ⊢s σ : Δ ->
  Δ ⊢ t : T ->
  Γ ⊢ t [ σ ] : T [ σ ]
| typing_cumu : forall Γ T i,
  Γ ⊢ T : 𝕊 i ->
  Γ ⊢ T : exp_set (1 + i)
| typing_conv : forall Γ t S T i,
  Γ ⊢ t : T ->
  Γ ⊢ T ≈ S : 𝕊 i ->
  Γ ⊢ t : S
with SubstTyping : Ctx -> Subst -> Ctx -> Prop :=
| subst_typing_id : forall Γ,
  ⊢ Γ ->
  Γ ⊢s subst_id : Γ
| subst_typing_shift : forall Γ T,
  ⊢ (T :: Γ) ->
  (T :: Γ) ⊢s ↑ : Γ
| subst_typing_comp : forall Γ1 Γ2 Γ3 σ1 σ2,
  Γ1 ⊢s σ1 : Γ2 ->
  Γ2 ⊢s σ2 : Γ3 ->
  Γ1 ⊢s σ2 ∘ σ1 : Γ3
| subst_typing_ext : forall Γ Δ σ t T i,
  Γ ⊢s σ : Δ ->
  Δ ⊢ T : 𝕊 i ->
  Γ ⊢ t : T [ σ ] ->
  Γ ⊢s subst_ext σ t : (T :: Δ)
| subst_typing_conv : forall Γ Δ Δ' σ,
  Γ ⊢s σ : Δ ->
  ⊢ Δ ≈ Δ' ->
  Γ ⊢s σ : Δ'
with EqExp : Ctx -> Exp -> Exp -> Exp -> Prop :=
| eq_exp_prop_nat : forall Γ Δ σ i,
  Γ ⊢s σ : Δ ->
  Γ ⊢ ℕ [ σ ] ≈ ℕ : 𝕊 i
| eq_exp_prop_set : forall Γ Δ σ i,
  Γ ⊢s σ : Δ ->
  Γ ⊢ 𝕊 i [ σ ] ≈ 𝕊 i : exp_set (1 + i)
| eq_exp_prop_pi : forall Γ Δ σ S T i,
  Γ ⊢s σ : Δ ->
  Δ ⊢ S : 𝕊 i ->
  (S :: Δ) ⊢ T : 𝕊 i ->
  Γ ⊢ exp_pi S T [ σ ] ≈ exp_pi (S [ σ ]) (T [subst_ext (σ ∘ ↑) (exp_var 0)]) : 𝕊 i
| eq_exp_prop_zero : forall Γ Δ σ,
  Γ ⊢s σ : Δ ->
  Γ ⊢ exp_zero ≈ exp_zero [ σ ] : ℕ
| eq_exp_prop_suc : forall Γ Δ t σ,
  Γ ⊢s σ : Δ ->
  Δ ⊢ t : ℕ ->
  Γ ⊢ exp_suc t [ σ ] ≈ exp_suc (t [ σ ]) : ℕ
| eq_exp_prop_app : forall Γ Δ r s σ S T i,
  Γ ⊢s σ : Δ ->
  Δ ⊢ r : exp_pi S T ->
  Δ ⊢ S : exp_set i ->
  (S :: Δ) ⊢ T : exp_set i ->
  Δ ⊢ s : S ->
  Γ ⊢ (r ▫ s) [ σ ] ≈ (r [ σ ]) ▫ (s [ σ ]) : T [ subst_ext σ (s [ σ ]) ]
| eq_exp_prop_rec : forall Γ Δ σ tz ts tn T i,
  Γ ⊢s σ : Δ ->
  (ℕ :: Δ) ⊢ T : 𝕊 i ->
  Δ ⊢ tz : T [| exp_zero ] ->
  (T :: ℕ :: Δ) ⊢ ts : T [ subst_ext ( ↑ ∘ ↑ ) (exp_suc (exp_var 1)) ] ->
  Δ ⊢ tn : ℕ ->
  Γ ⊢ exp_rec T tz ts tn [ σ ] ≈ exp_rec (T [q σ]) (tz [σ]) (ts [q (q σ)]) (tn [ σ ]) : T [ subst_ext σ (tn [ σ ]) ]
| eq_exp_prop_abs : forall Γ Δ σ t S T,
  Γ ⊢s σ : Δ ->
  (S :: Δ) ⊢ t : T ->
  Γ ⊢ (λ t) [ σ ] ≈ (λ (t [q σ])) : (exp_pi S T) [ σ ]
| eq_exp_comp_pi : forall Γ S S' T T' i, 
  Γ ⊢ S : 𝕊 i ->
  Γ ⊢ S ≈ S' : 𝕊 i ->
  (S :: Γ) ⊢ T ≈ T' : 𝕊 i ->
  Γ ⊢ exp_pi S T ≈ exp_pi S' T' : 𝕊 i
| eq_exp_comp_var : forall Γ n T,
  ⊢ Γ ->
  n : T ∈ Γ ->
  Γ ⊢ exp_var n ≈ exp_var n : T
| eq_exp_comp_zero : forall Γ,
  ⊢ Γ ->
  Γ ⊢ exp_zero ≈ exp_zero : ℕ
| eq_exp_comp_suc : forall Γ t t',
  Γ ⊢ t ≈ t' : ℕ ->
  Γ ⊢ exp_suc t ≈ exp_suc t' : ℕ
| eq_exp_comp_app : forall Γ r r' s s' S T i,
  Γ ⊢ S : 𝕊 i ->
  (S :: Γ) ⊢ T : 𝕊 i ->
  Γ ⊢ r ≈ r' : exp_pi S T ->
  Γ ⊢ s ≈ s' : S ->
  Γ ⊢ r ▫ s ≈ r' ▫ s' : T [| s ]
| eq_exp_comp_rec : forall Γ tz tz' ts ts' tn tn' T T' i,
  (ℕ :: Γ) ⊢ T : 𝕊 i ->
  Γ ⊢ tz ≈ tz' : T [| exp_zero ] ->
  (T :: ℕ :: Γ) ⊢ ts ≈ ts' : T [ subst_ext (↑ ∘ ↑) (exp_suc (exp_var 1)) ] ->
  Γ ⊢ tn ≈ tn' : ℕ ->
  (ℕ :: Γ) ⊢ T ≈ T' : 𝕊 i ->
  Γ ⊢ exp_rec T tz ts tn ≈ exp_rec T' tz' ts' tn' : T [| tn ]
| eq_exp_comp_abs : forall Γ t t' S T i,
  Γ ⊢ S : 𝕊 i ->
  (S :: Γ) ⊢ t ≈ t' : T ->
  Γ ⊢ (λ t) ≈ (λ t') : exp_pi S T
| eq_exp_comp_subst : forall Γ Δ t t' σ σ' T,
  Γ ⊢s σ ≈ σ' : Δ ->
  Δ ⊢ t ≈ t' : T ->
  Γ ⊢ t [ σ ] ≈ t' [ σ' ] : T [ σ ]
| eq_exp_beta_abs : forall Γ t s S T i,
  Γ ⊢ S : 𝕊 i ->
  (S :: Γ) ⊢ T : 𝕊 i ->
  (S :: Γ) ⊢ t : T ->
  Γ ⊢ s : S ->
  Γ ⊢ (λ t) ▫ s ≈ t [| s ] : T [| s ] 
| eq_exp_beta_rec_zero : forall Γ tz ts T i,
  (ℕ :: Γ) ⊢ T : 𝕊 i ->
  Γ ⊢ tz : T [| exp_zero ] ->
  (T :: ℕ :: Γ) ⊢ ts : T [ subst_ext (↑ ∘ ↑) (exp_suc (exp_var 1)) ] ->
  Γ ⊢ exp_rec T tz ts exp_zero ≈ tz : T [| exp_zero ]
| eq_exp_beta_rec_suc : forall Γ tz ts tn T i,
  (ℕ :: Γ) ⊢ T : 𝕊 i ->
  Γ ⊢ tz : T [| exp_zero ] ->
  (T :: ℕ :: Γ) ⊢ ts : T [ subst_ext (↑ ∘ ↑) (exp_suc (exp_var 1)) ] ->
  Γ ⊢ tn : ℕ ->
  Γ ⊢ exp_rec T tz ts (exp_suc tn) ≈ ts [ subst_ext (subst_ext subst_id tn) (exp_rec T tz ts tn) ] : T [| exp_suc tn ]
| eq_exp_eta_abs : forall Γ t S T i,
  Γ ⊢ S : 𝕊 i ->
  (S :: Γ) ⊢ T : 𝕊 i ->
  Γ ⊢ t : exp_pi S T ->
  Γ ⊢ t ≈ exp_abs (t [ ↑ ] ▫ (exp_var 0)) : exp_pi S T
| eq_exp_subst_id : forall Γ t T,
  Γ ⊢ t : T ->
  Γ ⊢ t [ subst_id ] ≈ t : T
| eq_exp_substs_shift : forall Γ S T n,
  n : T ∈ Γ ->
  ⊢ (S :: Γ) ->
  (S :: Γ) ⊢ exp_var n [ ↑ ] ≈ exp_var (1 + n) : T [ ↑ ]
| eq_exp_subst_comp : forall Γ1 Γ2 Γ3 σ1 σ2 t T,
  Γ1 ⊢s σ1 : Γ2 ->
  Γ2 ⊢s σ2 : Γ3 ->
  Γ3 ⊢ t : T ->
  Γ1 ⊢ t [ σ2 ∘ σ1 ] ≈ t [ σ2 ] [ σ1 ] : T [ σ2 ∘ σ1 ]
| eq_exp_subst_ext_var_0 : forall Γ Δ σ s S i,
  Γ ⊢s σ : Δ ->
  Δ ⊢ S : 𝕊 i ->
  Γ ⊢ s : S [ σ ] ->
  Γ ⊢ exp_var 0 [ subst_ext σ s ] ≈ s : S [ σ ] 
| eq_exp_subst_ext_var_sn : forall Γ Δ σ s S T n i,
  Γ ⊢s σ : Δ ->
  Δ ⊢ S : 𝕊 i ->
  Γ ⊢ s : S [ σ ] ->
  n : T ∈ Δ ->
  Γ ⊢ exp_var (1 + n) [ subst_ext σ s ] ≈ exp_var n [ σ ] : T [ σ ]
| eq_exp_conv : forall Γ t t' T T' i,
  Γ ⊢ t ≈ t' : T ->
  Γ ⊢ T ≈ T' : 𝕊 i ->
  Γ ⊢ t ≈ t' : T'
| eq_exp_cumu : forall Γ T T' i,
  Γ ⊢ T ≈ T' : 𝕊 i ->
  Γ ⊢ T ≈ T' : exp_set (1 + i)
| eq_exp_sym : forall Γ t t' T,
  Γ ⊢ t ≈ t' : T ->
  Γ ⊢ t' ≈ t : T
| eq_exp_trans : forall Γ t1 t2 t3 T,
  Γ ⊢ t1 ≈ t2 : T ->
  Γ ⊢ t2 ≈ t3 : T ->
  Γ ⊢ t1 ≈ t3 : T
with EqSubst : Ctx -> Subst -> Subst -> Ctx -> Prop :=
| eq_subst_comp_id : forall Γ,
  ⊢ Γ ->
  Γ ⊢s subst_id ≈ subst_id : Γ
| eq_subst_comp_shift : forall T Γ,
  ⊢ (T :: Γ) ->
  (T :: Γ) ⊢s ↑ ≈ ↑ : Γ
| eq_subst_comp_comp : forall Γ1 Γ2 Γ3 σ1 σ1' σ2 σ2',
  Γ1 ⊢s σ1 ≈ σ1' : Γ2 ->
  Γ2 ⊢s σ2 ≈ σ2' : Γ3 ->
  Γ1 ⊢s (σ2 ∘ σ1) ≈ (σ2' ∘ σ1') : Γ3
| eq_subst_comp_ext : forall Γ Δ σ σ' t t' T i,
  Γ ⊢s σ ≈ σ' : Δ ->
  Δ ⊢ T : 𝕊 i ->
  Γ ⊢ t ≈ t' : T [ σ ] ->
  Γ ⊢s subst_ext σ t ≈ subst_ext σ' t' : (T :: Δ)
| eq_subst_id_l : forall Γ Δ σ,
  Γ ⊢s σ : Δ ->
  Γ ⊢s subst_id ∘ σ ≈ σ : Δ
| eq_subst_id_r : forall Γ Δ σ,
  Γ ⊢s σ : Δ ->
  Γ ⊢s σ ∘ subst_id ≈ σ : Δ
| eq_subst_assoc : forall Γ1 Γ2 Γ3 Γ4 σ1 σ2 σ3,
  Γ1 ⊢s σ1 : Γ2 ->
  Γ2 ⊢s σ2 : Γ3 ->
  Γ3 ⊢s σ3 : Γ4 ->
  Γ1 ⊢s (σ3 ∘ σ2) ∘ σ1 ≈ σ3 ∘ (σ2 ∘ σ1) : Γ4
| eq_subst_prop_ext : forall Γ1 Γ2 Γ3 σ τ t T i,
  Γ1 ⊢s τ : Γ2 ->
  Γ2 ⊢s σ : Γ3 ->
  Γ3 ⊢ T : 𝕊 i ->
  Γ2 ⊢ t : T [ σ ] ->
  Γ1 ⊢s subst_ext σ t ∘ τ ≈ subst_ext (σ ∘ τ) (t [ τ ]) : (T :: Γ3) 
| eq_subst_eta_ext : forall Γ Δ σ T,
  Γ ⊢s σ : (T :: Δ) ->
  Γ ⊢s σ ≈ subst_ext (↑ ∘ σ) (exp_var 0 [σ]) : (T :: Δ)
| eq_subst_prop_shift : forall Γ Δ σ t T i,
  Γ ⊢s σ : Δ ->
  Δ ⊢ T : 𝕊 i ->
  Γ ⊢ t : T [ σ ] ->
  Γ ⊢s ↑ ∘ (subst_ext σ t) ≈ σ : Δ
| eq_subst_sym : forall Γ Δ σ σ',
  Γ ⊢s σ ≈ σ' : Δ ->
  Γ ⊢s σ' ≈ σ : Δ
| eq_subst_trans : forall Γ Δ σ1 σ2 σ3,
  Γ ⊢s σ1 ≈ σ2 : Δ ->
  Γ ⊢s σ2 ≈ σ3 : Δ ->
  Γ ⊢s σ1 ≈ σ3 : Δ
| eq_subst_conv : forall Γ Δ Δ' σ σ',
  Γ ⊢s σ ≈ σ' : Δ ->
  ⊢ Δ ≈ Δ' ->
  Γ ⊢s σ ≈ σ' : Δ'
where "⊢ Γ" := (WfCtx Γ) and
      "⊢ Γ ≈ Γ'" := (EqCtx Γ Γ') and 
      "Γ ⊢ t : T" := (Typing Γ t T) and 
      "Γ ⊢s σ : Δ" := (SubstTyping Γ σ Δ) and 
      "Γ ⊢ t ≈ t' : T" := (EqExp Γ t t' T) and 
      "Γ ⊢s σ ≈ σ' : Δ" := (EqSubst Γ σ σ' Δ).

Scheme wf_ctx_ind := Induction for WfCtx Sort Prop
  with eq_ctx_ind := Induction for EqCtx Sort Prop
  with typing_ind := Induction for Typing Sort Prop
  with subst_typing_ind := Induction for SubstTyping Sort Prop
  with eq_exp_ind := Induction for EqExp Sort Prop 
  with eq_subst_ind := Induction for EqSubst Sort Prop.

Combined Scheme wf_ctx_eq_ctx_typing_subst_typing_eq_exp_eq_subst_mutind from wf_ctx_ind, eq_ctx_ind, typing_ind, subst_typing_ind, eq_exp_ind, eq_subst_ind.

Hint Constructors InCtx WfCtx EqCtx Typing SubstTyping EqExp EqSubst : core.
Hint Constructors nat : core.

Lemma wf_typ_in_wf_ctx : forall Γ T n,
  ⊢ Γ ->
  n : T ∈ Γ ->
  exists i, Γ ⊢ T : exp_set i.
Proof.
  intros. induction H0; eauto.
  - inversion H; subst. exists i. econstructor; eauto.
  - inversion H; subst. apply IHInCtx in H3.
    destruct H3 as [i1].
    exists i1; eauto. eapply typing_conv with (T := (𝕊 i1) [ ↑ ]); eauto.
Qed.

Lemma wf_typ_subst_inv : forall Γ Δ σ T i,
  Γ ⊢s σ : Δ ->
  Δ ⊢ T : exp_set i ->
  Γ ⊢ T [ σ ] : exp_set i.
Proof.
  intros. eauto. 
Qed.

Lemma eq_typ_subst_inv : forall Γ Δ σ σ' T T' i,
  Γ ⊢s σ : Δ ->
  Γ ⊢s σ ≈ σ' : Δ ->
  Δ ⊢ T ≈ T' : exp_set i ->
  Γ ⊢ T [σ] ≈ T' [σ'] : exp_set i.
Proof.
  intros. eapply eq_exp_conv; eauto.
Qed.

Lemma wf_typ_cumu_larger_add : forall Γ T i k,
  Γ ⊢ T : exp_set i ->
  Γ ⊢ T : exp_set (k + i).
Proof.
  intros.
  induction k; simpl in *; eauto.
Qed.

Lemma wf_typ_cumu_larger : forall Γ T i j,
  i <= j ->
  Γ ⊢ T : exp_set i ->
  Γ ⊢ T : exp_set j.
Proof.
  intros. assert (exists k, j = k + i).
  - clear H0. induction H; eauto.
    exists 0; auto.
    destruct IHle as [k]. exists (S k); lia.
  - destruct H1 as [k]. rewrite H1.
    apply wf_typ_cumu_larger_add. auto.
Qed.

Hint Resolve wf_typ_subst_inv : core.

Lemma eq_ctx_sym : forall Γ Γ',
  ⊢ Γ ≈ Γ' ->
  ⊢ Γ' ≈ Γ.
Proof.
  intros. induction H; eauto.
Qed.

Lemma eq_exp_refl : forall Γ t T,
  Γ ⊢ t : T ->
  Γ ⊢ t ≈ t : T.
Proof.
  eauto.
Qed.

Lemma eq_subst_refl : forall Γ σ Δ,
  Γ ⊢s σ : Δ ->
  Γ ⊢s σ ≈ σ : Δ.
Proof.
  eauto.
Qed.

Lemma eq_ctx_refl : forall Γ,
  ⊢ Γ ->
  ⊢ Γ ≈ Γ.
Proof.
  intros. induction H; auto.
  - econstructor; eauto.
Qed.

Lemma eq_ctx_typing : forall Γ Δ t T,
  Γ ⊢ t : T ->
  ⊢ Γ ≈ Δ ->
  Δ ⊢ t : T.
Proof.
Admitted.

Lemma var0_subst_comp : forall Γ Δ σ T i,
  Γ ⊢s σ : Δ ->
  Δ ⊢ T : 𝕊 i ->
  ⊢ (T [σ] :: Γ) ->
  (T [σ] :: Γ) ⊢ exp_var 0 : T [σ ∘ ↑].
Proof.
  intros. inversion H1; subst; auto. 
  eapply typing_conv with (T := T [σ] [↑]) (i:=i); eauto.
  eapply eq_exp_conv with (T := exp_set i [σ ∘ ↑]); eauto.
Qed.

Lemma suc_var1_nat : forall Γ T i,
  ⊢ Γ ->
  (ℕ :: Γ) ⊢ T : 𝕊 i ->
  (T :: ℕ :: Γ) ⊢ exp_suc (exp_var 1) : ℕ [↑ ∘ ↑].
Proof.
  intros. eapply typing_conv with (T := ℕ) (i:=0); eauto.
  - econstructor. eapply typing_conv with (T := ℕ [↑] [↑]).
    eapply typing_var; eauto.
    eapply eq_exp_trans with (t2 := ℕ [↑ ∘ ↑]) (T:=exp_set 0); eauto.
    + eapply eq_exp_conv with (T := exp_set 0 [↑ ∘ ↑]); eauto.
      eapply eq_exp_sym; eauto.
      eapply eq_exp_subst_comp; eauto.
      eapply eq_exp_prop_set; eauto.
      econstructor; eauto.
    + eapply eq_exp_prop_nat; eauto.
      econstructor; eauto.
  - eapply eq_exp_sym. eapply eq_exp_prop_nat; eauto.
      econstructor; eauto.
  Unshelve. all: eauto.
Qed.

Lemma ctx_upshift_same_type_twice : forall Γ T i,
  ⊢ Γ ->
  Γ ⊢ T : 𝕊 i ->
  (T [↑] :: T :: Γ) ⊢s ↑ : (T :: Γ).
Proof.
  intros. econstructor; eauto.
  econstructor; eauto.
Qed.

Lemma var0_subst_id : forall Γ T i,
  ⊢ Γ ->
  Γ ⊢ T : 𝕊 i ->
  (T :: Γ) ⊢ exp_var 0 : T [↑] [subst_id].
Proof.
  intros.  eapply typing_conv with (T := T [↑]) (i:=i); eauto.
  apply eq_exp_sym; eauto.
Qed.

Lemma eq_typ_subst_comp : forall Γ1 Γ2 Γ3 σ1 σ2 T i,
  Γ1 ⊢s σ1 : Γ2 ->
  Γ2 ⊢s σ2 : Γ3 ->
  Γ3 ⊢ T : exp_set i ->
  Γ1 ⊢ T [σ2 ∘ σ1] ≈ T [σ2] [σ1] : exp_set i.
Proof.
  intros. 
  apply eq_exp_conv with (T := exp_set i [σ2 ∘ σ1]) (i := 1 + i); eauto.
Qed.

Lemma subst_ext_shift_twice_comp_subst0_eq_id : forall T Γ i,
  ⊢ Γ ->
  Γ ⊢ T : exp_set i ->
  (T :: Γ) ⊢s subst_ext (↑ ∘ ↑) (exp_var 0) ∘ (subst_ext subst_id (exp_var 0)) ≈ subst_id : (T :: Γ).
Proof with eauto using ctx_upshift_same_type_twice, var0_subst_id, eq_typ_subst_comp.
  intros. apply eq_subst_trans with (σ2 := subst_ext ((↑ ∘ ↑) ∘ (subst_ext subst_id (exp_var 0))) (exp_var 0 [ subst_ext subst_id (exp_var 0)])); eauto.
  - eapply eq_subst_prop_ext with (Γ2:=T [↑] :: T :: Γ); eauto.
    + econstructor; eauto. eapply var0_subst_id; eauto. 
    + econstructor; eauto; econstructor; eauto.
      econstructor; eauto.
    + eapply var0_subst_comp; eauto.
      econstructor; eauto.
  - assert ((T [↑] :: T :: Γ) ⊢s ↑ : (T :: Γ)). {
      repeat (econstructor; eauto).
    }
    assert (⊢ (T [↑] :: T :: Γ)). {
      repeat (econstructor; eauto).
    }
    assert ((T :: Γ) ⊢ exp_var 0 [subst_ext subst_id (exp_var 0)] : T [↑]). {
      inversion H2; subst; auto.
      eapply typing_conv with (T := T [↑] [↑] [subst_ext subst_id (exp_var 0)]) (i := i0); eauto...
        do 4 (econstructor; eauto).
      eapply eq_exp_trans with (t2:=T [↑] [↑ ∘ subst_ext subst_id (exp_var 0)]); eauto.
        eapply eq_exp_conv with (T := exp_set i0 [↑ ∘ subst_ext subst_id (exp_var 0)]) (i:=1 + i0).
        eapply eq_exp_sym; eauto. eapply eq_exp_subst_comp; eauto... repeat (econstructor; eauto). 
      eapply eq_exp_trans with (t2:=T [↑] [subst_id]); eauto...
      eapply eq_typ_subst_inv...
      econstructor; eauto...
    }
    assert ((T :: Γ) ⊢s subst_ext subst_id (exp_var 0) : (T [↑] :: T :: Γ)). {
      econstructor; eauto.
      eapply var0_subst_id; eauto.
    }
    eapply eq_subst_trans with (σ2:=subst_ext (↑ ∘ (↑ ∘ subst_ext subst_id (exp_var 0))) (exp_var 0 [subst_ext subst_id (exp_var 0)])).
    eapply eq_subst_comp_ext; eauto.
    eapply eq_exp_conv with (T := T [(↑ ∘ ↑)] [subst_ext subst_id (exp_var 0)]) (i:=i); eauto.
      econstructor; eauto. eapply eq_exp_refl; eauto. eapply var0_subst_comp; eauto.
      eapply eq_exp_conv with (T := exp_set i [(↑ ∘ ↑) ∘ subst_ext subst_id (exp_var 0)]) (i:=1+i); eauto.
      eapply eq_exp_sym...
      eapply eq_exp_prop_set; eauto.
    eapply eq_subst_trans with (σ2:=subst_ext (↑ ∘ subst_id) (exp_var 0 [subst_ext subst_id (exp_var 0)])).
      eapply eq_subst_comp_ext; eauto. eapply eq_subst_comp_comp with (Γ2:=T :: Γ); eauto.
      eapply eq_subst_prop_shift with (T := T [↑]); eauto...
      eapply eq_exp_conv with (T := T [↑ ∘ ↑]  [subst_ext subst_id (exp_var 0)]) (i := i). 
        eapply eq_exp_refl. 
        eapply typing_subst with (Δ:=T [↑] :: T :: Γ); eauto...
        eapply var0_subst_comp; eauto...
        eapply eq_exp_trans with (t2 := T [(↑ ∘ ↑) ∘ subst_ext subst_id (exp_var 0)]); eauto.
        eapply eq_exp_conv with (T := exp_set i [(↑ ∘ ↑) ∘ subst_ext subst_id (exp_var 0)]); eauto.
        eapply eq_exp_sym. eapply eq_exp_subst_comp; eauto...
          econstructor; eauto.
          eapply eq_typ_subst_inv; eauto.
    eapply eq_subst_trans with (σ2:=subst_ext (↑ ∘ subst_id) (exp_var 0))...
      eapply eq_subst_comp_ext; eauto... econstructor; eauto...
      eapply eq_exp_conv with (T := T [↑] [subst_id]); eauto.
      eapply eq_exp_subst_ext_var_0; eauto. eapply var0_subst_id; eauto.
      eapply eq_exp_sym... eapply eq_typ_subst_comp; eauto.
    eapply eq_subst_trans with (σ2:=subst_ext (↑ ∘ subst_id) (exp_var 0 [subst_id])); eauto.
      eapply eq_subst_comp_ext; eauto. econstructor; eauto.
      eapply eq_exp_sym. eapply eq_exp_subst_id; eauto.
      eapply typing_conv with (T := T [↑] [subst_id]) (i:=i); eauto.
      eapply var0_subst_id; eauto.
      eapply eq_exp_sym; eauto.
      eapply eq_typ_subst_comp; eauto.
Qed.
 
Lemma presupposition : 
  (forall Γ, ⊢ Γ -> ⊢ Γ ) /\ 
  (forall Γ Δ, ⊢ Γ ≈ Δ -> ⊢ Γ /\ ⊢ Δ) /\
  (forall Γ t T, Γ ⊢ t : T -> ⊢ Γ /\ exists i, Γ ⊢ T : exp_set i) /\
  (forall Γ σ Δ, Γ ⊢s σ : Δ -> ⊢ Γ /\ ⊢ Δ) /\
  (forall Γ t t' T, Γ ⊢ t ≈ t' : T -> ⊢ Γ /\ Γ ⊢ t : T /\ Γ ⊢ t' : T /\ exists i, Γ ⊢ T : exp_set i) /\
  (forall Γ σ σ' Δ, Γ ⊢s σ ≈ σ' : Δ -> ⊢ Γ /\ Γ ⊢s σ : Δ /\ Γ ⊢s σ' : Δ /\ ⊢ Δ).
Proof.
  apply wf_ctx_eq_ctx_typing_subst_typing_eq_exp_eq_subst_mutind; intros; try solve [ intuition; eauto ].
  - intuition.
    eapply wf_typ_in_wf_ctx; eauto.
  - intuition. exists i; eauto.
    eapply wf_typ_subst_inv with (Δ:=ℕ :: Γ); eauto.
    econstructor; eauto.
  - intuition. destruct H2 as [i1]. destruct H3 as [i2].
    exists (max i i2). econstructor; eauto.
    + eapply wf_typ_cumu_larger with (i:=i); auto. lia.
    + eapply wf_typ_cumu_larger with (i:=i2); auto. lia.
  - intuition. exists i.
    unfold subst0. 
    eapply wf_typ_subst_inv with (Δ:=S :: Γ); eauto.
    econstructor; econstructor; eauto.
  - intuition. destruct H3 as [i]. eauto. 
  - inversion H; subst; eauto. 
  - intuition. 
    + eapply typing_conv with (T := 𝕊 i [ σ ]); eauto.
    + eapply typing_pi; eauto.
      eapply typing_conv with (T:=𝕊 i [subst_ext (σ ∘ ↑) (exp_var 0)]) (i := 1 + i); eauto.
      econstructor; eauto.
      * econstructor; eauto.
        eapply typing_conv with (T := S [σ] [↑]) (i:=i); eauto.
        eapply eq_exp_conv with (T := 𝕊 i [σ ∘ ↑]) (i := 1 + i); eauto.
        apply eq_exp_sym. eapply eq_exp_subst_comp; eauto.
        econstructor; eauto.
      * eapply eq_exp_prop_set with (Δ := S :: Δ); eauto.
        destruct H4 as [i1].
        eapply subst_typing_ext with (i := i).
        eapply subst_typing_comp with (Γ2:=Γ); eauto. auto.
        eapply typing_conv with (T := S [ σ ] [ ↑ ]) (i := i); eauto.
        eapply eq_exp_sym.
        eapply eq_exp_conv with (T := 𝕊 i [σ ∘ ↑]) (i := 1 + i); eauto.
        econstructor; eauto.
    + eauto. 
  - intuition.
    + eapply typing_conv with (T:=T [subst_ext subst_id s] [σ]) (i:=i); eauto.
      econstructor; eauto. econstructor; eauto.
      apply eq_exp_trans with (t2:=T [subst_ext subst_id s ∘ σ]); eauto.
      eapply eq_exp_conv with (T:=exp_set i [subst_ext subst_id s ∘ σ]); eauto.
      eapply eq_exp_sym. eapply eq_exp_subst_comp; eauto. econstructor; eauto.
      repeat (econstructor; eauto).
      eapply eq_typ_subst_inv; eauto. repeat (econstructor; eauto).
      eapply eq_subst_trans with (σ2:=subst_ext (subst_id ∘ σ) (s [σ])); eauto.
      eapply eq_subst_prop_ext; eauto.
      eapply eq_subst_comp_ext; eauto.
      eapply eq_exp_conv with (T:=S [σ]) (i:=i); eauto.
      eapply eq_exp_refl; eauto.
      eapply eq_typ_subst_inv; eauto.
    + eapply typing_conv with (T := T [subst_ext (σ ∘ ↑) (exp_var 0)] [| s [σ] ]) (i:=i).
      * eapply typing_app with (S:=S [σ]) (i:=i); eauto.
        eapply wf_typ_subst_inv; eauto.
        econstructor; eauto.
        eapply typing_conv with (T := S [σ] [↑]) (i := i); eauto.
        eapply eq_exp_conv with (T := (exp_set i) [σ ∘ ↑]) (i := 1 + i); eauto.
        eapply eq_exp_sym. eauto.
        econstructor; eauto.
      * assert (Γ ⊢s subst_ext subst_id (s [σ]) : (S [σ] :: Γ)). {
          repeat (econstructor; eauto).
        }
        assert (Γ ⊢ s [σ] : S [σ] [subst_id]). {
          repeat (econstructor; eauto).
        }
        assert (Γ ⊢s subst_ext (σ ∘ ↑) (exp_var 0) ∘ subst_ext subst_id (s [σ]) ≈  subst_ext σ (s [σ]) : (S :: Δ)). {
          eapply eq_subst_trans with (σ2 := subst_ext ((σ ∘ ↑) ∘ subst_ext subst_id (s [σ])) ((exp_var 0) [subst_ext subst_id (s [σ])])); eauto.
            eapply eq_subst_prop_ext; eauto. eapply var0_subst_comp; eauto.
          eapply eq_subst_comp_ext; eauto.
            eapply eq_subst_trans with (σ2:=σ ∘ ↑ ∘ subst_ext subst_id (s [σ])); eauto.
            eapply eq_subst_trans with (σ2:=σ ∘ subst_id); eauto.
            eapply eq_subst_comp_comp; eauto.
          eapply eq_exp_conv with (T := S [σ] [subst_id]) (i := i); eauto.
          eapply eq_exp_trans with (t2 := S [σ ∘ ↑ ∘ subst_ext subst_id (s [σ])]); eauto.
          apply eq_exp_trans with (t2 := S [σ ∘ subst_id]); eauto.
            eapply eq_exp_sym. eapply eq_typ_subst_comp; eauto.
            eapply eq_typ_subst_inv; eauto. eapply eq_subst_comp_comp; eauto.
          eapply eq_typ_subst_inv; eauto. econstructor; eauto.
          eapply eq_subst_sym. eapply eq_subst_assoc; eauto.
        }
        unfold subst0. eapply eq_exp_trans with (t2 := T [subst_ext (σ ∘ ↑) (exp_var 0) ∘ subst_ext subst_id (s [σ])]); eauto.
        eapply eq_exp_conv with (T := exp_set i  [subst_ext (σ ∘ ↑) (exp_var 0) ∘ subst_ext subst_id (s [σ])]) (i := 1 + i); eauto.
        eapply eq_exp_sym; eauto. eapply eq_exp_subst_comp with (Γ2:=S [σ] :: Γ); eauto.
        econstructor; eauto.
        eapply var0_subst_comp; eauto.
        eapply eq_exp_prop_set with (Δ:=S :: Δ). 
        eapply subst_typing_comp with (Γ2:=S [σ] :: Γ); eauto. econstructor; eauto.
        eapply var0_subst_comp; eauto.
        eapply eq_typ_subst_inv; eauto. 
        eapply subst_typing_comp with (Γ2:=S [σ] :: Γ); eauto.
        econstructor; eauto. 
        eapply var0_subst_comp; eauto.
    + exists i; eauto.
      eapply wf_typ_subst_inv with (σ := subst_ext σ (s [σ])); eauto.
      econstructor; eauto.
  - intuition; destruct H8 as [i1].
    + eapply typing_conv with (T := T [subst_ext subst_id tn] [σ]) (i:=i); eauto.
      eapply eq_exp_trans with (t2:=T [subst_ext subst_id tn ∘ σ]); eauto.
      eapply eq_exp_sym; eauto.
      eapply eq_exp_conv with (T := exp_set i [subst_ext subst_id tn ∘ σ]) (i:=1+i); eauto.
      eapply eq_exp_subst_comp with (Γ3:=ℕ::Δ); eauto.
      eapply subst_typing_ext; eauto.
      eapply eq_exp_prop_set with (Δ:=ℕ::Δ); eauto. 
      econstructor; eauto. econstructor; eauto.
      eapply eq_typ_subst_inv; eauto.
      repeat (econstructor; eauto).
      eapply eq_subst_trans with (σ2:=subst_ext (subst_id ∘ σ) (tn [σ])); eauto.
      eapply eq_subst_prop_ext; eauto.
      eapply eq_subst_comp_ext; eauto. eapply eq_exp_conv with (T :=  ℕ [subst_id] [σ]) (i:=0); eauto.
      * econstructor; eauto. eapply eq_exp_conv with (T := ℕ); eauto.
      * eapply eq_exp_conv with (T := exp_set 0 [subst_id ∘ σ]); eauto.
    + eapply typing_conv with (T := T [q σ] [|tn [σ]]) (i:=i1); eauto.
      eapply typing_rec with (i:=i1).
      * admit. (* 1, *)
      * admit. (* 2, *)
      * admit. (* 3, *)
      * econstructor; eauto.
      * unfold q. admit. (* 4, *)
    + exists i; eauto.
      eapply wf_typ_subst_inv with (σ := subst_ext σ (tn [σ])); eauto.
      econstructor; eauto.
  - intuition; inversion H; subst; destruct H3 as [i1]; eauto.
    + eapply typing_conv with (T := exp_pi (S [σ]) (T [subst_ext (σ ∘ ↑) (exp_var 0)])) (i:=max i i1); eauto.
      * econstructor; eauto. econstructor; eauto.
        econstructor; eauto.
        eapply var0_subst_comp; eauto.
      * apply eq_exp_sym; eauto.
        eapply eq_exp_prop_pi; eauto.
        -- eapply wf_typ_cumu_larger with (i:=i); auto. lia.
        -- eapply wf_typ_cumu_larger with (i:=i1); auto. lia.
    + exists (max i i1); eauto.
      eapply wf_typ_subst_inv; eauto.
      econstructor; eauto. 
      * eapply wf_typ_cumu_larger with (i:=i); auto. lia.
      * eapply wf_typ_cumu_larger with (i:=i1); auto. lia.
  - intuition. 
    econstructor; eauto. 
    eapply eq_ctx_typing; eauto using eq_ctx_refl. 
  - intuition.
    eapply wf_typ_in_wf_ctx; eauto.
  - intuition; eauto.
    + eapply typing_conv with (T := T [| s' ]) (i := i); eauto.
      apply eq_exp_conv with (T := 𝕊 i [|s']) (i := 1 + i); eauto.
      eapply eq_exp_comp_subst; eauto.
      eapply eq_subst_comp_ext; eauto.
      econstructor; eauto. econstructor; eauto.
    + exists i. eapply wf_typ_subst_inv; eauto.
      econstructor; eauto.
  (* eq_exp_comp_rec *)
  - intuition; eauto.
    + eapply typing_conv with (T := T' [| tn' ]) (i:=i); eauto.
      * eapply typing_rec; eauto.
       eapply typing_conv with (T:= T [|exp_zero]) (i:=i); eauto.
       eapply eq_typ_subst_inv; eauto;
       repeat (econstructor; eauto). 
       eapply typing_conv with (T := T [subst_ext (↑ ∘ ↑) (exp_suc (exp_var 1))]) (i:=i); eauto.
       eapply eq_ctx_typing with (Γ:=(T :: ℕ :: Γ)); eauto. econstructor; eauto. apply eq_ctx_refl; auto.
       eapply eq_typ_subst_inv; eauto.
       econstructor; eauto. eapply suc_var1_nat; eauto.
       eapply eq_subst_comp_ext; eauto.
       eapply eq_exp_refl. eapply suc_var1_nat; eauto.
      * eapply eq_typ_subst_inv; eauto. econstructor; eauto.
        econstructor; eauto. econstructor; eauto. 
    + exists i. eapply wf_typ_subst_inv; eauto. econstructor; eauto.
  - intuition; eauto. 
    + destruct H5 as [i1]. exists (max i i1); eauto.
      econstructor; eauto.
      * eapply wf_typ_cumu_larger with (i:=i); auto. lia.
      * eapply wf_typ_cumu_larger with (i:=i1); auto. lia.
  - intuition; eauto.
    + destruct H7 as [i]. eapply typing_conv with (T := T [σ']) (i:=i); eauto.
      eapply eq_typ_subst_inv; eauto.
    + destruct H7 as [i]. eauto. 
  - intuition; eauto. 
    + econstructor; eauto. econstructor; eauto.
    + destruct H6 as [i1]. exists i1; auto.
      eapply wf_typ_subst_inv; eauto. econstructor; eauto.
  - intuition; eauto.
    + eapply typing_conv with (T := T [subst_ext (↑ ∘ ↑) (exp_suc (exp_var 1))] [subst_ext (subst_ext subst_id tn)
          (exp_rec T tz ts tn)]) (i:=i); eauto.
      repeat (econstructor; eauto).
      admit. (* 5, *** *)
    + exists i; auto.
      eapply wf_typ_subst_inv with (Δ:=ℕ :: Γ); eauto. 
      econstructor; eauto. econstructor; eauto.
  - intuition. econstructor; eauto.
    eapply typing_conv with (T := T [subst_ext (↑ ∘ ↑) (exp_var 0)] [| exp_var 0] ) (i := i); eauto.
    eapply typing_app with (S := S [↑]) (i := i).
    inversion t2; subst; eauto.
    + eapply wf_typ_subst_inv; eauto.
      econstructor; eauto. econstructor; eauto.
      eapply var0_subst_comp; eauto.
    + econstructor; eauto. 
    + econstructor; eauto.
    + unfold subst0.
      apply eq_exp_trans with (t2 := T [subst_ext (↑ ∘ ↑) (exp_var 0) ∘ subst_ext subst_id (exp_var 0)]); eauto.
      eapply eq_exp_sym; eauto. 
      eapply eq_exp_conv with (T := exp_set i [subst_ext (↑ ∘ ↑) (exp_var 0) ∘ subst_ext subst_id (exp_var 0)]); eauto.
      eapply eq_exp_subst_comp with (Γ2:=S [↑] :: S :: Γ); eauto.
      eapply subst_typing_ext with (Δ:=S :: Γ); eauto.
      eapply typing_conv with (T := S [↑]); eauto.
        econstructor; eauto. econstructor; eauto. 
        eapply var0_subst_comp; eauto. 
        eapply eq_exp_prop_set with (Δ:=S :: Γ); eauto.
        eapply subst_typing_comp with (Γ2:=S [↑] :: S :: Γ); eauto.
        econstructor; eauto. eapply typing_conv with (T := S [↑]); eauto.
        econstructor; eauto. econstructor; eauto. eapply var0_subst_comp; eauto.
      eapply eq_exp_trans with (t2 := T [subst_id]); eauto.
      eapply eq_typ_subst_inv; eauto.
      eapply subst_typing_comp with (Γ2:=S [↑] :: S :: Γ); eauto.
        econstructor; eauto. eapply typing_conv with (T := S [↑]); eauto. 
        econstructor; eauto. econstructor; eauto. 
        eapply var0_subst_comp; eauto.
      eapply subst_ext_shift_twice_comp_subst0_eq_id; eauto.
  - intuition. destruct H1 as [i]. eauto.
  - intuition. inversion H; subst; eauto.
    inversion H; subst; auto.
    apply wf_typ_in_wf_ctx in i; eauto.
    destruct i as [i1]. exists i1; eauto.
  - intuition; destruct H5 as [i]; eauto.
    + eapply typing_conv with (T := T [σ2]  [σ1]) (i := i); eauto.
      eapply eq_exp_conv with (T := 𝕊 i [σ2 ∘ σ1]) (i := 1 + i); eauto.
  - intuition. 
    destruct H5 as [i1].
    eapply typing_conv with (T:=S [ ↑ ] [subst_ext σ s]) (i:=i).
    econstructor; eauto. econstructor; eauto. econstructor; eauto.
    eapply eq_exp_trans with (t2:=S [↑ ∘ (subst_ext σ s)]); eauto.
    apply eq_exp_sym. 
    eapply eq_exp_conv with (T := exp_set i [↑ ∘ subst_ext σ s]) (i:=1+i); eauto.
    eapply eq_exp_subst_comp; eauto;
    repeat (econstructor; eauto). 
    repeat (econstructor; eauto). 
    eapply eq_typ_subst_inv; eauto.
    repeat (econstructor; eauto).
  (* eq_subst_ext *)
  - intuition; eauto. 
    + apply wf_typ_in_wf_ctx in i0 as Hwft; eauto. 
      destruct Hwft as [i1].
      eapply typing_conv with (T:=T [↑] [subst_ext σ s] ) (i:=i1); eauto.
      eapply typing_subst with (Δ:=S :: Δ); eauto.
      eapply eq_exp_trans with (t2:=T [↑ ∘ subst_ext σ s]); eauto.
      eapply eq_exp_conv with (T:=exp_set i1 [↑ ∘ subst_ext σ s]) (i:=1+i1); eauto.
      apply eq_exp_sym; eauto. eapply eq_exp_subst_comp with (Γ2:=S::Δ);  eauto.
      eapply eq_exp_prop_set with (Δ:=Δ); eauto. 
      eapply subst_typing_comp with (Γ2:=S :: Δ); eauto.
      eapply eq_typ_subst_inv; eauto.
      apply subst_typing_comp with (Γ2:=S :: Δ); eauto.
    + apply wf_typ_in_wf_ctx in i0; eauto. 
      destruct i0 as [i1]. eauto.
  (* eq_subst_shift *)
  - intuition. inversion H; subst; eauto. 
  - intuition; eauto.
    econstructor; eauto.
    eapply typing_conv with (i:=i); eauto.
    eapply eq_typ_subst_inv; eauto. 
  - intuition; eauto.
    econstructor; eauto.
    eapply typing_conv with (i:=i); eauto.
    eapply eq_exp_conv with (T := 𝕊 i [σ ∘ τ]) (i := 1 + i); eauto.
  - intuition; eauto. inversion H1; subst; eauto.
    econstructor; eauto.
    eapply typing_conv with (T := T [↑] [σ]) (i := i); eauto.
    eapply eq_exp_sym. eapply eq_exp_conv with (T := exp_set i [↑ ∘ σ]); eauto.
  - intuition. econstructor; eauto.
    econstructor; eauto.
    econstructor; eauto.
  Unshelve. all : eauto. 
Admitted.
  

