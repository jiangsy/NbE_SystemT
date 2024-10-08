Require Import Coq.Lists.List.
Require Import Lia.

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

Notation "'λ' t" := (exp_abs t)
  (at level 55). 

Notation "↑" := es_shift.

Notation " t [ σ ] " := (exp_subst t σ)
  (at level 52, left associativity).

Notation "r ▫ s" := (exp_app r s)
  (at level 53, left associativity).

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
  | styping_ext : forall Γ Δ σ s S,
    Γ ⊢s σ : Δ ->
    Γ ⊢ s : S ->
    Γ ⊢s (es_ext σ s) : (S :: Δ)
where "Γ ⊢ t : T" := (Typing Γ t T) and
      "Γ ⊢s σ : Δ" := (SubstTyping Γ σ Δ).

Scheme typing_ind := Induction for Typing Sort Prop
  with subst_typing_ind := Induction for SubstTyping Sort Prop.

Combined Scheme typing_subst_typing_mutind from typing_ind, subst_typing_ind.

Inductive Ne : Set :=
  | ne_v (vi : nat)
  | ne_app (u : Ne) (v : Nf)
  | ne_rec (T : Typ) (vz vs : Nf) (u : Ne)
with Nf : Set :=
  | nf_ne (u : Ne)
  | nf_abs (v : Nf)
  | nf_zero
  | nf_suc (v : Nf).

Reserved Notation "Γ ⊢ t ≈ t' : T"
  (at level 55, t at next level, t' at next level, no associativity).
Reserved Notation "Γ ⊢s σ ≈ σ' : Δ"
  (at level 55, σ at next level, σ' at next level, no associativity).
Inductive ExpEq : Ctx -> Exp -> Exp -> Typ -> Prop := 
| exp_eq_beta_abs : forall Γ s t S T,
    (S :: Γ) ⊢ t : T ->
    Γ ⊢ s : S ->
    Γ ⊢ exp_app (exp_abs t) s ≈ exp_subst t (es_ext es_id s) : T
| exp_eq_beta_rec_zero : forall Γ tz ts T,
    Γ ⊢ tz : T ->
    Γ ⊢ ts : ℕ → T → T ->
    Γ ⊢ exp_rec T tz ts exp_zero ≈ tz : T
| exp_eq_beta_rec_suc : forall Γ tz ts tn T,
    Γ ⊢ tz : T ->
    Γ ⊢ ts : ℕ → T → T ->
    Γ ⊢ tn : ℕ ->
    Γ ⊢ exp_rec T tz ts (exp_suc tn) ≈ exp_app (exp_app ts tn) (exp_rec T tz ts tn) : T
| exp_eq_subst_shift : forall Γ i T S,
    nth_error Γ i = Some T ->
    (S :: Γ) ⊢ exp_subst (exp_var i) es_shift ≈ exp_var (1 + i) : T
| exp_eq_subst_id : forall Γ t T,
    Γ ⊢ t : T ->
    Γ ⊢ exp_subst t es_id ≈ t : T
| exp_eq_subst_ext0 : forall Γ Δ σ s S,
    Γ ⊢s σ : Δ ->
    Γ ⊢ s : S ->
    Γ ⊢ exp_subst (exp_var 0) (es_ext σ s) ≈ s : S
| exp_eq_subst_exts : forall Γ Δ σ s S T i,
    Γ ⊢s σ : Δ ->
    Γ ⊢ s : S ->
    nth_error Δ i = Some T ->
    Γ ⊢ exp_subst (exp_var (1 + i)) (es_ext σ s) ≈ exp_subst (exp_var i) σ : T
| exp_eq_prop_app : forall Γ Δ σ r s S T,
    Γ ⊢s σ : Δ ->
    Δ ⊢ r : S → T ->
    Δ ⊢ s : S ->
    Γ ⊢ exp_subst (exp_app r s) σ ≈ exp_app (exp_subst r σ) (exp_subst s σ) : T
| exp_eq_prop_comp : forall Γ1 Γ2 Γ3 τ σ t T,
    Γ1 ⊢s τ : Γ2 ->
    Γ2 ⊢s σ : Γ3 ->
    Γ3 ⊢ t : T ->
    Γ1 ⊢ exp_subst (exp_subst t σ) τ ≈ exp_subst t (σ ∘ τ) : T
| exp_eq_prop_zero : forall Γ σ Δ,
    Γ ⊢s σ : Δ ->
    Γ ⊢ exp_subst exp_zero σ ≈ exp_zero : ℕ
| exp_eq_prop_suc : forall Γ σ Δ t,
    Γ ⊢s σ : Δ ->
    Δ ⊢ t : ℕ ->
    Γ ⊢ exp_subst (exp_suc t) σ ≈ exp_suc (exp_subst t σ) : ℕ
| exp_eq_prop_rec : forall Γ Δ σ tz ts tn T,
    Γ ⊢s σ : Δ ->
    Δ ⊢ tz : T ->
    Δ ⊢ ts : ℕ → T → T ->
    Δ ⊢ tn : ℕ ->
    Γ ⊢ exp_subst (exp_rec T tz ts tn) σ ≈ exp_rec T (exp_subst tz σ) (exp_subst ts σ) (exp_subst tn σ) : T
| exp_eq_comp_i : forall Γ i T,
    nth_error Γ i = Some T ->
    Γ ⊢ exp_var i ≈ exp_var i : T
| exp_eq_comp_app : forall Γ r r' s s' S T,
    Γ ⊢ r ≈ r' : S → T ->
    Γ ⊢ s ≈ s' : S ->
    Γ ⊢ exp_app r s ≈ exp_app r' s' : T
| exp_eq_comp_zero : forall Γ,
    Γ ⊢ exp_zero ≈ exp_zero : ℕ
| exp_eq_comp_suc : forall Γ t t',
    Γ ⊢ t ≈ t' : ℕ ->
    Γ ⊢ exp_suc t ≈ exp_suc t' : ℕ
| exp_eq_comp_rec : forall Γ tz tz' ts ts' tn tn' T,
    Γ ⊢ tz ≈ tz' : T ->
    Γ ⊢ ts ≈ ts' : ℕ → T → T ->
    Γ ⊢ tn ≈ tn' : ℕ ->
    Γ ⊢ exp_rec T tz ts tn ≈ exp_rec T tz' ts' tn' : T 
| exp_eq_comp_subst : forall Γ Δ σ σ' t t' T,
    Γ ⊢s σ ≈ σ' : Δ ->
    Δ ⊢ t ≈ t' : T ->
    Γ ⊢ exp_subst t σ ≈ exp_subst t' σ' : T
| exp_eq_symm : forall Γ t t' T,
    Γ ⊢ t ≈ t' : T ->
    Γ ⊢ t' ≈ t : T
| exp_eq_trans : forall Γ t1 t2 t3 T,
    Γ ⊢ t1 ≈ t2 : T ->
    Γ ⊢ t2 ≈ t3 : T ->
    Γ ⊢ t1 ≈ t3 : T
| exp_eq_ext_xi : forall Γ t t' S T,
    (S :: Γ) ⊢ t ≈ t' : T ->
    Γ ⊢ (exp_abs t) ≈ (exp_abs t') : S → T
| exp_eq_ext_eta : forall Γ t S T,
    Γ ⊢ t : S → T ->
    Γ ⊢ t ≈ exp_abs (exp_app (exp_subst t es_shift) (exp_var 0)) : S → T
| exp_eq_ext_prop : forall Γ Δ σ t S T,
    Γ ⊢s σ : Δ ->
    (S :: Δ) ⊢ t : T ->
    Γ ⊢ exp_subst (exp_abs t) σ ≈ exp_abs (exp_subst t (es_ext (σ ∘ ↑) (exp_var 0))) : S → T
with SubstEq : Ctx -> Subst -> Subst -> Ctx -> Prop :=
| subst_eq_shift_ext : forall Γ Δ σ s S,
    Γ ⊢s σ : Δ ->
    Γ ⊢ s : S ->
    Γ ⊢s es_shift ∘ (es_ext σ s) ≈ σ : Δ
| subst_eq_idl : forall Γ Δ σ,
    Γ ⊢s σ : Δ ->
    Γ ⊢s (es_id ∘ σ) ≈ σ : Δ
| subst_eq_idr : forall Γ Δ σ,
    Γ ⊢s σ : Δ ->
    Γ ⊢s (σ ∘ es_id) ≈ σ : Δ
| subst_eq_assoc : forall Γ1 Γ2 Γ3 Γ4 σ1 σ2 σ3,
    Γ4 ⊢s σ3 : Γ3 ->
    Γ3 ⊢s σ2 : Γ2 ->
    Γ2 ⊢s σ1 : Γ1 ->
    Γ4 ⊢s (σ1 ∘ σ2) ∘ σ3 ≈ σ1 ∘ (σ2 ∘ σ3) : Γ1
| subst_eq_ext : forall Γ S, 
    (S :: Γ) ⊢s es_id ≈ es_ext es_shift (exp_var 0) : (S :: Γ)
| subst_eq_prop : forall Γ Δ Γ' σ τ s S,
    Γ ⊢s τ : Γ' ->
    Γ' ⊢s σ : Δ ->
    Γ' ⊢ s : S ->
    Γ ⊢s (es_ext σ s) ∘ τ ≈ es_ext (σ ∘ τ) (exp_subst s τ) : (S :: Δ)
| subst_eq_compat_shift : forall Γ S,
    (S :: Γ) ⊢s ↑ ≈ ↑ : Γ
| subst_eq_compat_id : forall Γ,
    Γ ⊢s es_id ≈ es_id : Γ
| subst_eq_compat_ext : forall Γ Δ σ σ' s s' S,
    Γ ⊢s σ ≈ σ' : Δ ->
    Γ ⊢ s ≈ s' : S ->
    Γ ⊢s es_ext σ s ≈ es_ext σ' s' : (S :: Δ)
| subst_eq_compat_comp : forall Γ1 Γ2 Γ3 σ σ' τ τ',
    Γ1 ⊢s τ ≈ τ' : Γ2 ->
    Γ2 ⊢s σ ≈ σ' : Γ3 ->
    Γ1 ⊢s σ ∘ τ ≈ σ' ∘ τ' : Γ3 
| subst_eq_symm : forall Γ Δ σ σ',
    Γ ⊢s σ ≈ σ' : Δ ->
    Γ ⊢s σ' ≈ σ : Δ
| subst_eq_trans : forall Γ Δ σ1 σ2 σ3,
    Γ ⊢s σ1 ≈ σ2 : Δ ->
    Γ ⊢s σ2 ≈ σ3 : Δ ->
    Γ ⊢s σ1 ≈ σ3 : Δ
where "Γ ⊢ t ≈ t' : T" := (ExpEq Γ t t' T) and 
      "Γ ⊢s σ ≈ σ' : Δ" := (SubstEq Γ σ σ' Δ).
    
Lemma exp_eq_subst_eq_refl : 
  (forall Γ t T, Γ ⊢ t : T -> Γ ⊢ t ≈ t : T) /\
  (forall Γ σ Δ, Γ ⊢s σ : Δ -> Γ ⊢s σ ≈ σ : Δ).
Proof.
  apply typing_subst_typing_mutind; intros; eauto using ExpEq, SubstEq.
Qed.

Corollary exp_eq_refl : forall Γ t T, 
  Γ ⊢ t : T -> 
  Γ ⊢ t ≈ t : T.
Proof.
  specialize exp_eq_subst_eq_refl; intuition; eauto.
Qed.

Corollary subst_eq_refl : forall Γ Δ σ,
  Γ ⊢s σ : Δ ->
  Γ ⊢s σ ≈ σ : Δ.
Proof.
  specialize exp_eq_subst_eq_refl; intuition; eauto.
Qed.

Scheme exp_eq_ind := Induction for ExpEq Sort Prop
  with subst_eq_ind := Induction for SubstEq Sort Prop.

Combined Scheme exp_eq_subst_eq_mutind from exp_eq_ind, subst_eq_ind.

Lemma syn_exp_eq_subst_eq_typing_subst_typing : 
  (forall Γ t t' T, Γ ⊢ t ≈ t' : T -> Γ ⊢ t : T /\ Γ ⊢ t' : T ) /\
  (forall Γ σ σ' Δ, Γ ⊢s σ ≈ σ' : Δ -> Γ ⊢s σ : Δ /\ Γ ⊢s σ' : Δ).
Proof with eauto using Typing, SubstTyping.
  apply exp_eq_subst_eq_mutind; intros; intuition...
  - econstructor.
    eapply typing_subst with (Δ := S :: Δ)...
Qed.

Corollary syn_exp_eq_typing : forall Γ t t' T,
  Γ ⊢ t ≈ t' : T -> Γ ⊢ t : T /\ Γ ⊢ t' : T.
Proof.
  pose proof syn_exp_eq_subst_eq_typing_subst_typing. intuition.
Qed.

Corollary syn_exp_eq_typing_l : forall Γ t t' T,
  Γ ⊢ t ≈ t' : T -> Γ ⊢ t : T.
Proof.
  pose proof syn_exp_eq_subst_eq_typing_subst_typing. intuition.
  apply H0 in H. intuition.
Qed.

Corollary syn_exp_eq_typing_r : forall Γ t t' T,
  Γ ⊢ t ≈ t' : T -> Γ ⊢ t' : T.
Proof.
  pose proof syn_exp_eq_subst_eq_typing_subst_typing. intuition.
  apply H0 in H. intuition.
Qed.

Corollary syn_subst_eq_subst_typing_l : forall Γ σ σ' Δ, 
  Γ ⊢s σ ≈ σ' : Δ -> Γ ⊢s σ : Δ.
Proof.
  pose proof syn_exp_eq_subst_eq_typing_subst_typing. intuition.
  apply H1 in H. intuition.
Qed.

Corollary syn_subst_eq_subst_typing_r : forall Γ σ σ' Δ, 
  Γ ⊢s σ ≈ σ' : Δ -> Γ ⊢s σ' : Δ.
Proof.
  pose proof syn_exp_eq_subst_eq_typing_subst_typing. intuition.
  apply H1 in H. intuition.
Qed.

Definition syn_pred (t : Exp) : Exp :=
  exp_rec ℕ exp_zero (exp_abs (exp_abs (exp_var 1))) t.

Lemma syn_pred_typing : forall Γ t,
  Γ ⊢ t : ℕ ->
  Γ ⊢ syn_pred t : ℕ.
Proof with eauto using Typing.
  intros. unfold syn_pred...
Qed.

Lemma exp_eq_pred_suc : forall Γ t,
  Γ ⊢ t : ℕ ->
  Γ ⊢ syn_pred (exp_suc t) ≈ t : ℕ.
Proof with eauto 6 using Typing, SubstTyping, ExpEq, SubstEq.
  intros. unfold syn_pred. 
  apply exp_eq_trans with (t2:=(λ (λ exp_var 1)) ▫ t ▫ (exp_rec ℕ exp_zero (λ (λ exp_var 1)) t)).
  apply exp_eq_beta_rec_suc... 
  apply exp_eq_trans with (t2:= (exp_subst (λ exp_var 1) (es_ext es_id t))▫ (exp_rec ℕ exp_zero (λ (λ exp_var 1)) t))...
  eapply exp_eq_comp_app with (S:=ℕ)...
  eapply exp_eq_beta_abs... econstructor... apply exp_eq_refl...
  eapply exp_eq_trans with (t2:=(exp_abs (exp_subst (exp_var 1) (es_ext ((es_ext es_id t) ∘ ↑) (exp_var 0)))) ▫ exp_rec ℕ exp_zero (λ (λ exp_var 1)) t); eauto.
  eapply exp_eq_comp_app with (S:=ℕ); eauto.
  eapply exp_eq_ext_prop with (Δ:=ℕ :: Γ)...
  eapply exp_eq_refl...
  eapply exp_eq_trans with (t2:=(exp_var 1 [es_ext (es_ext es_id t ∘ ↑) (exp_var 0)]) [ es_ext es_id (exp_rec ℕ exp_zero (λ (λ exp_var 1)) t)]); eauto.
  eapply exp_eq_beta_abs... eapply typing_subst with (Δ:=ℕ :: ℕ :: Γ)...
  eapply exp_eq_trans with (t2:=(exp_var 0 [(es_ext es_id t ∘ ↑)]) [ es_ext es_id (exp_rec ℕ exp_zero (λ (λ exp_var 1)) t)]); eauto...
  replace 1 with (1 + 0) at 1.
  eapply exp_eq_comp_subst with (Δ:=ℕ::Γ); eauto. apply subst_eq_refl...
  eapply exp_eq_subst_exts with (S:=ℕ)... lia. 
  eapply exp_eq_trans with (t2:=exp_var 0 [es_ext es_id t ∘ ↑] [es_ext es_id (exp_rec ℕ exp_zero (λ (λ exp_var 1)) t)]); eauto.
  eapply exp_eq_refl... eapply typing_subst with (Δ:=ℕ :: Γ)... 
  eapply exp_eq_trans with (t2:=exp_var 0 [es_ext ( es_id ∘ ↑ ) ( t [ ↑ ]) ] [es_ext es_id (exp_rec ℕ exp_zero (λ (λ exp_var 1)) t)]); eauto.
  eapply exp_eq_comp_subst with (Δ:=ℕ :: Γ)... eapply subst_eq_refl...
  eapply exp_eq_trans with (t2:= (t [ ↑ ]) [es_ext es_id (exp_rec ℕ exp_zero (λ (λ exp_var 1)) t)])...
  eapply exp_eq_comp_subst... eapply subst_eq_refl...
  eapply exp_eq_trans with (t2:=t [ es_id ])...
  eapply exp_eq_trans with (t2:=t [ ↑ ∘ es_ext es_id (exp_rec ℕ exp_zero (λ (λ exp_var 1)) t)])...
  eapply exp_eq_prop_comp...
  eapply exp_eq_comp_subst...
Qed.

Fixpoint nf_to_exp (w : Nf) : Exp :=
  match w with 
  | nf_abs w' => exp_abs (nf_to_exp w')
  | nf_suc w' => exp_suc (nf_to_exp w')
  | nf_zero => exp_zero
  | nf_ne u => ne_to_exp u
  end
with ne_to_exp (u : Ne) : Exp :=
  match u with
  | ne_app u' w => exp_app (ne_to_exp u') (nf_to_exp w)
  | ne_rec T wz ws un => exp_rec T (nf_to_exp wz) (nf_to_exp ws) (ne_to_exp un)
  | ne_v i => exp_var i
  end.

Coercion nf_to_exp : Nf >-> Exp.
Coercion ne_to_exp : Ne >-> Exp.
