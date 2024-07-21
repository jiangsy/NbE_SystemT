Require Import Coq.Program.Equality.

Require Import nbe.systemt.intensional.syntax.
Require Import nbe.systemt.intensional.semantic.

Definition SemTyp := D -> Prop.

Definition SemEnv := Env -> Prop.

Definition Top : SemTyp := 
 fun d => forall n, exists v, Rⁿᶠ ⦇ n ⦈ d ↘ v.

Notation "d ∈ ⊤" := (Top d)
   (at level 55, no associativity).

Definition Bot : Dne -> Prop :=
 fun e => forall n, exists u, Rⁿᵉ ⦇ n ⦈ e ↘ u.

Notation "e ∈ ⊥" := (Bot e)
   (at level 55, no associativity).

Reserved Notation "d ∈ '𝒩' "
  (at level 55, no associativity).
Inductive SemNat : SemTyp :=
 | snat_zero : d_zero ∈ 𝒩
 | snat_suc : forall d,
    d ∈ 𝒩 ->
    d_suc d ∈ 𝒩
 | snat_bot : forall e,
    e ∈ ⊥ ->
    SemNat (d_ne e)
where " d ∈ '𝒩' " := (SemNat d).

Definition SemArr : SemTyp -> SemTyp -> SemTyp :=
   fun A B f => forall a, A a -> exists b, B b /\ f ∙ a ↘ b.

Fixpoint interp_typ (T : Typ) : SemTyp :=
   match T with 
   | typ_nat => SemNat 
   | typ_arr S' T' => SemArr (interp_typ S') (interp_typ T')
   end.

Notation "⟦ T ⟧T" := (interp_typ T)
   (at level 55, no associativity).

(* Scheme d_ind := Induction for D Sort Prop
  with dne_ind := Induction for Dne Sort Prop.

Combined Scheme d_dne_mutind from d_ind, dne_ind. *)

Lemma bot_subset_T_subset_top : forall T,
   (forall e, e ∈ ⊥ -> ⟦ T ⟧T (d_ne e)) /\
   (forall d, ⟦ T ⟧T d -> d ∈ ⊤ ).
Proof with eauto using SemNat, RNeRel, RNfRel.
   intros. induction T; split; try simpl...
   - intros. dependent induction H.
     + unfold Top. intros...
     + admit.
     + admit.
   - intros. admit.
Admitted.