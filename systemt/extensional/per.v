Require Import Coq.Program.Equality.

Require Import nbe.systemt.extensional.syntax.
Require Import nbe.systemt.extensional.semantic.

Definition SemTyp := D -> D -> Prop.

Definition SemTypTop (d d' : Dnf) : Prop :=
  forall n, exists w, Rⁿᶠ ⦇ n ⦈ d ↘ w /\ Rⁿᶠ ⦇ n ⦈ d' ↘ w.

Definition SemTypBot (e e' : Dne) : Prop :=
  forall n, exists u, Rⁿᵉ ⦇ n ⦈ e ↘ u /\ Rⁿᵉ ⦇ n ⦈ e' ↘ u.

Notation "e ≈ e' ∈ ⊥" := (SemTypBot e e')
  (at level 55, no associativity).

Notation "d ≈ d' ∈ ⊤" := (SemTypTop d d')
  (at level 55, no associativity).

Hint Constructors AppRel RNfRel RNeRel : core.

Lemma sem_bot_symm : forall e e',
  e ≈ e' ∈ ⊥ -> e' ≈ e ∈ ⊥.
Proof.
  intros. unfold SemTypBot in *. intros.
  specialize (H n). destruct H as [u [Hrnee Hrene']].
  eauto.
Qed.

Lemma sem_bot_trans : forall e1 e2 e3,
  e1 ≈ e2 ∈ ⊥ -> e2 ≈ e3 ∈ ⊥ -> e1 ≈ e3 ∈ ⊥.
Proof.
  intros. unfold SemTypBot in *. intros.
  specialize (H n). specialize (H0 n).
  destruct H as [u1 [Hrnee1 Hrnee2]].
  destruct H0 as [u2 [Hrnee2' Hrnee3]].
  eapply rne_det in Hrnee2; eauto. subst. eauto.
Qed.

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

Lemma sem_bot_rec : forall e e' dz dz' ds ds' T,
  e ≈ e' ∈ ⊥ ->
  dz ≈ dz' ∈ ⊤ ->
  ds ≈ ds' ∈ ⊤ ->
  dne_rec T dz ds e ≈ dne_rec T dz' ds' e' ∈ ⊥.
Proof.
  intros. unfold SemTypBot in *. unfold SemTypTop in *.
  intros. specialize (H n). specialize (H0 n). specialize (H1 n).
  destruct H as [u [Hrnee Hrnee']].
  destruct H0 as [wz [Hrnfdz Hrnfdz']].
  destruct H1 as [ws [Hrnfds Hrnfds']].
  eauto.
Qed.

Lemma sem_top_zero : 
  (dnf_reif ℕ d_zero) ≈ (dnf_reif ℕ d_zero) ∈ ⊤.
Proof.
  unfold SemTypTop. intros; eauto.
Qed.

Lemma sem_top_suc : forall a a',
  (dnf_reif ℕ a) ≈ (dnf_reif ℕ a') ∈ ⊤ ->
  (dnf_reif ℕ (d_suc a)) ≈ (dnf_reif ℕ (d_suc a')) ∈ ⊤.
Proof.
  intros. unfold SemTypTop in *. intros.
  specialize (H n).
  destruct H as [w [Hrnfa Hrnfa']].
  eauto.
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

Definition Realize (T : Typ) (A : SemTyp) : Prop :=
  (forall a a', A a a' -> dnf_reif T a ≈ dnf_reif T a' ∈ ⊤) /\
  (forall e e', e ≈ e' ∈ ⊥ -> A (d_refl T e) (d_refl T e')).

Notation "T ⊩ A" := (Realize T A)
  (at level 55, no associativity).

Inductive SemTypNat : D -> D -> Prop :=
  | snat_zero: SemTypNat d_zero d_zero
  | snat_suc : forall a a',
      SemTypNat a a' ->
      SemTypNat (d_suc a) (d_suc a')
  | snat_ne : forall e e',
      e ≈ e' ∈ ⊥ ->
      SemTypNat (d_refl ℕ e) (d_refl ℕ e').

Notation "'𝒩'" := SemTypNat.

Notation "a ≈ a' ∈ '𝒩'" := (SemTypNat a a')
  (at level 55, no associativity).

Lemma nat_realize_sem_nat : ℕ ⊩ 𝒩.
Proof.
  unfold Realize. split; intros.
  - induction H; unfold SemTypTop; intros; eauto.
    + unfold SemTypTop in IHSemTypNat. specialize (IHSemTypNat n).
      destruct IHSemTypNat as [w [Hrnfa Hrnfa']].
      eauto.
    + unfold SemTypBot in H. specialize (H n).
      destruct H as [u]. intuition. eauto.
  - constructor; auto.
Qed.

Definition SemAbs (S T : SemTyp) : SemTyp :=
  fun f f' => forall a a', S a a' -> exists b b', f ∙ a ↘ b /\ f' ∙ a' ↘ b' /\ T b b'.

Notation "S ⇒ T" := (SemAbs S T)  (at level 55, right associativity).

Lemma sem_abs_intros : forall S T A B,
  S ⊩ A -> T ⊩ B -> (S → T) ⊩ (A ⇒ B).
Proof.
  intros. unfold Realize in *. split.
  - intros. apply sem_typ_top_abs. intros. unfold SemAbs in H1.  
    intuition.
    apply H4 in H2. apply H1 in H2. 
    destruct H2 as [b [b']]. exists b, b'. intuition.
  - intros. unfold SemAbs. intros.
    exists (d_refl T (dne_app e (dnf_reif S a))), (d_refl T (dne_app e' (dnf_reif S a'))); intuition; eauto.
    + eauto using sem_typ_bot_app.
Qed.

Lemma sem_nat_symm : forall a a',
  a ≈ a' ∈ 𝒩 -> a' ≈ a ∈ 𝒩.
Proof.
  intros.
  induction H; eauto using SemTypNat, sem_bot_symm.
Qed.

Lemma sem_nat_trans : forall a1 a2 a3,
  a1 ≈ a2 ∈ 𝒩 -> a2 ≈ a3 ∈ 𝒩 -> a1 ≈ a3 ∈ 𝒩.
Proof.
  intros. generalize dependent a3. induction H; intros; eauto.
  - dependent destruction H0.
    eauto using SemTypNat.
  - dependent destruction H0.
    eauto using SemTypNat, sem_bot_trans.
Qed.

Fixpoint interp_typ (T : Typ) : SemTyp :=
  match T with 
  | ℕ => 𝒩
  | S' → T' => (interp_typ S') ⇒ (interp_typ T')
  end.

Notation "⟦ T ⟧T" := (interp_typ T).

Notation "a ≈ a' ∈ ⟦ T ⟧T" := ((interp_typ T) a a') 
  (at level 55, a' at next level, no associativity).

Lemma sem_typ_symm: forall a a' T,
  a ≈ a' ∈ ⟦ T ⟧T ->
  a' ≈ a ∈ ⟦ T ⟧T.
Proof.
  intros. generalize dependent a. generalize dependent a'. induction T; intros.
  - simpl in *. apply sem_nat_symm. eauto.
  - simpl in *. unfold SemAbs in *. intros.
    apply IHT1 in H0.
    apply H in H0.
    destruct H0 as [b [b']].
    exists b', b. intuition.
Qed.

Lemma sem_typ_trans : forall a1 a2 a3 T,
  a1 ≈ a2 ∈ ⟦ T ⟧T ->
  a2 ≈ a3 ∈ ⟦ T ⟧T ->
  a1 ≈ a3 ∈ ⟦ T ⟧T.
Proof.
  intros. generalize dependent a1. generalize dependent a2. generalize dependent a3.
  induction T; intros.
  - simpl in *. eapply sem_nat_trans; eauto.
  - simpl in *. unfold SemAbs in *. intros.
    apply sem_typ_symm in H1 as H1'.
    eapply IHT1 in H1'; eauto.
    apply H in H1 as IH1.
    apply H0 in H1' as IH2.
    destruct IH1 as [b1 [b2]].
    destruct IH2 as [b2' [b3]].
    intuition.
    eapply app_det in H2; eauto. subst.
    exists b1, b3; intuition.
    eapply IHT2; eauto.
Qed.