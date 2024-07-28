Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.

Require Import nbe.systemt.extensional.syntax.
Require Import nbe.systemt.extensional.semantic.
Require Import nbe.systemt.extensional.completeness.

Definition TypeStructure := Exp -> D -> Prop.

Definition KripkeTypeStructure := Ctx -> TypeStructure.

Fixpoint subst_from_weaken (Δ : Ctx) : Subst :=
  match Δ with
  | nil => es_id 
  | T :: Δ' => es_comp (subst_from_weaken Δ') es_shift
  end.

Hint Constructors SubstTyping : core.

Lemma subst_from_weaken_sound : forall Γ Δ,
  (Δ ++ Γ) ⊢s (subst_from_weaken Δ) : Γ.
Proof.
  intros. induction Δ; simpl in *; eauto.
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

Definition KripkeCandidateSpaceUpper (T : Typ) (Γ : Ctx) (t : Exp) (d : D) : Prop :=
  Γ ⊢ t : T /\
  forall Δ, exists w, Rⁿᶠ ⦇ length (Δ ++ Γ) ⦈ (dnf_reif T d) ↘ w /\ (Δ ++ Γ) ⊨ t [subst_from_weaken Δ] ≈ w : T.

Definition KripkeCandidateSpaceLower (T : Typ) (Γ : Ctx) (t : Exp) (e : Dne) : Prop :=
  Γ ⊢ t : T /\
  forall Δ, exists u, Rⁿᵉ ⦇ length (Δ ++ Γ) ⦈ e ↘ u /\ (Δ ++ Γ) ⊨ t [subst_from_weaken Δ] ≈ u : T.

Notation " t × d ∈ ⌈ T ⌉ ⦇ Γ ⦈" := (KripkeCandidateSpaceUpper T Γ t d)
  (at level 55, d at next level, T at next level, no associativity).

Notation " t × e ∈ ⌊ T ⌋ ⦇ Γ ⦈" := (KripkeCandidateSpaceLower T Γ t e)
  (at level 55, e at next level, T at next level, no associativity).

Lemma nat_lower_subset_upper : forall Γ t e,
  t × e ∈ ⌊ ℕ ⌋ ⦇ Γ ⦈ ->
  t × d_refl ℕ e ∈ ⌈ ℕ ⌉ ⦇ Γ ⦈.
Proof.  
  intros. unfold KripkeCandidateSpaceLower in *. unfold KripkeCandidateSpaceUpper in *. intros.
  intuition.
  specialize (H1 Δ).
  destruct H1 as [u]. intuition.
  exists (nf_ne u). intuition.
Qed.

Definition KripkeArrSpace (S T : Typ) (Γ : Ctx) (A B : KripkeTypeStructure): TypeStructure :=
  fun t f =>
    Γ ⊢ t : S → T /\
    forall Δ a s, A (Δ ++ Γ) s a -> exists b, f ∙ a ↘ b /\ B (Δ ++ Γ) (t [subst_from_weaken Δ]) b.

Fixpoint interp_typ (T : Typ) : KripkeTypeStructure :=
  match T with 
  | ℕ => KripkeCandidateSpaceUpper ℕ
  | S' → T' => fun Γ => KripkeArrSpace S' T' Γ (interp_typ S') (interp_typ T')
  end.

Notation "t × d ∈ ⟦ T ⟧ ⦇ Γ ⦈" := ((interp_typ T) Γ t d)
  (at level 55, d at next level, T at next level, no associativity).

Lemma in_typ_structure_wf : forall Γ t T d,
  t × d ∈ ⟦ T ⟧ ⦇ Γ ⦈ -> Γ ⊢ t : T.
Proof.
  intros. generalize dependent t. generalize dependent d. generalize dependent Γ.
  induction T; intros; simpl in *.
  - unfold KripkeCandidateSpaceUpper in H. intuition.
  - unfold KripkeArrSpace in H. intuition.
Qed.