Require Import nbe.systemt.extensional.syntax.
Require Import nbe.systemt.extensional.semantic.

Definition SemTyp := D -> D -> Prop.

Notation "d ∈! T" := (T d d) 
 (at level 55, no associativity).

Definition SemTypTop (d d' : Dnf) : Prop :=
  forall n, exists w, Rⁿᶠ ⦇ n ⦈ d ↘ w /\ Rⁿᶠ ⦇ n ⦈ d' ↘ w.

Definition SemTypBot (e e' : Dne) : Prop :=
  forall n, exists u, Rⁿᵉ ⦇ n ⦈ e ↘ u /\ Rⁿᵉ ⦇ n ⦈ e' ↘ u.

Notation " e ≈ e' ∈ ⊥" := (SemTypBot e e')
  (at level 55, no associativity).

Notation " d ≈ d' ∈ ⊤" := (SemTypTop d d')
  (at level 55, no associativity).

Hint Constructors RNfRel RNeRel : core.

Lemma sem_typ_bot_var : forall i,
  (dne_l i) ≈ (dne_l i) ∈ ⊥.
Proof.
  intros. unfold SemTypBot. intros.
  exists (ne_v (n - i - 1)). split; eauto.
Qed.

Lemma sem_typ_bot_app : forall e e' d d',
  e ≈ e' ∈ ⊥ ->
  d ≈ d' ∈ ⊤ ->
  (dne_app e d) ≈ (dne_app e' d') ∈ ⊥.
Proof.
  intros. unfold SemTypBot in *. unfold SemTypTop in *. intros.
  specialize (H n).
  specialize (H0 n).
  destruct H as [u [Hrnee Hrnee']].
  destruct H0 as [w [Hrnfd Hrnfd']].
  exists (ne_app u w). intuition.
Qed.

Lemma sem_typ_top_ne : forall e e',
  e ≈ e' ∈ ⊥ ->
  dnf_reif ℕ (d_refl ℕ e) ≈ dnf_reif ℕ (d_refl ℕ e') ∈ ⊤.
Proof.
  intros. unfold SemTypTop. unfold SemTypBot in *. intros.
  specialize (H n).
  destruct H as [u [Hrnee Hrnee']].
  exists (nf_ne u). intuition.
Qed.

Lemma sem_typ_top_abs : forall f f' S T,
  (forall e e', e ≈ e' ∈ ⊥ -> 
    exists b b', f ∙ (d_refl S e) ↘ b /\ f' ∙ (d_refl S e') ↘ b' /\ 
      (dnf_reif T b) ≈ (dnf_reif T b') ∈ ⊤) ->
  (dnf_reif (S → T) f) ≈ (dnf_reif (S → T) f') ∈ ⊤.
Proof.
  intros. unfold SemTypTop. intros.
  assert (dne_l n ≈ dne_l n ∈ ⊥) by (unfold SemTypBot; intros; eauto).
  apply H in H0.
  destruct H0 as [b [b']]. intuition.
  unfold SemTypTop in H3. specialize (H3 (1 + n)). destruct H3 as [w].
  exists (nf_abs w); intuition; eauto.
Qed.
