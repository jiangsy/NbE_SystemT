Require Import Coq.Lists.List.
Require Import Coq.Program.Equality. 
Require Import Lia.

Require Import ptt.syntax.def.
Require Import ptt.syntax.def_rule_full.
Require Import ptt.syntax.def_rule_concise.

Scheme wf_ctx_ind := Induction for def_rule_concise.WfCtx Sort Prop 
  with eq_ctx_ind := Induction for def_rule_concise.EqCtx Sort Prop
  with typing_ind := Induction for def_rule_concise.Typing Sort Prop
  with subst_typing_ind := Induction for def_rule_concise.SubstTyping Sort Prop
  with eq_exp_ind := Induction for def_rule_concise.EqExp Sort Prop 
  with eq_subst_ind := Induction for def_rule_concise.EqSubst Sort Prop.

Combined Scheme concise_wf_ctx_eq_ctx_typing_subst_typing_eq_exp_eq_subst_mutind from wf_ctx_ind, eq_ctx_ind, typing_ind, subst_typing_ind, eq_exp_ind, eq_subst_ind.

#[local] Hint Constructors def_rule_full.WfCtx def_rule_full.EqCtx def_rule_full.Typing def_rule_full.SubstTyping def_rule_full.EqExp def_rule_full.EqSubst : core.

Lemma typing_pi_inv' : forall Γ S T R,
  (Γ ⊢ exp_pi S T : R)%F ->
  exists k, (Γ ⊢ S : exp_set k)%F /\ ((S :: Γ) ⊢ T : exp_set k)%F.
Proof.
  intros. 
  dependent induction H; intros; eauto.
Qed.

Lemma typing_pi_inv : forall Γ t S T,
  (Γ ⊢ t : exp_pi S T)%F ->
  exists k, (Γ ⊢ S : exp_set k)%F /\ ((S :: Γ) ⊢ T : exp_set k)%F.
Proof.
  intros. apply typing_presup in H. intuition.
  destruct H1 as [i].
  eapply typing_pi_inv'; eauto.
Qed.

Lemma rule_concise_sound : 
  (forall Γ, ⊢ Γ -> (⊢ Γ)%F) /\
  (forall Γ Δ, ⊢ Γ ≈ Δ -> (⊢ Γ ≈ Δ)%F) /\
  (forall Γ t T, Γ ⊢ t : T -> (Γ ⊢ t : T)%F) /\
  (forall Γ σ Δ, Γ ⊢s σ : Δ -> (Γ ⊢s σ : Δ)%F) /\
  (forall Γ t t' T, Γ ⊢ t ≈ t' : T -> (Γ ⊢ t ≈ t' : T)%F) /\
  (forall Γ σ σ' Δ, Γ ⊢s σ ≈ σ' : Δ -> (Γ ⊢s σ ≈ σ': Δ)%F).
Proof.
  apply concise_wf_ctx_eq_ctx_typing_subst_typing_eq_exp_eq_subst_mutind; intros; eauto.
  - apply typing_presup in H as Hwf. intuition.
    destruct H1 as [i1]. econstructor; eauto.
  - apply eq_exp_presup in H0 as Hwf. intuition. 
    econstructor; eauto.
    eapply eq_ctx_typing; eauto.
    eapply eq_ctx_eq_exp; eauto.
  - eapply typing_presup in H as Hwf. intuition.
    inversion H0; subst; eauto.
  - apply typing_pi_inv in H as Hwf. 
    destruct Hwf as [i1]. intuition.
    eauto.
  - apply typing_pi_inv in H0 as Hwf. 
    destruct Hwf as [i1]. intuition.
    eauto.
  - econstructor; eauto.
    eapply eq_exp_presup in H. intuition.
  - apply eq_exp_presup in H as Hwf. intuition.
     apply typing_pi_inv in H3 as Hwf.   
    destruct Hwf as [i1]. intuition. eauto.
  - econstructor; eauto.
    apply eq_exp_presup in H2. intuition.
  - eapply eq_exp_presup in H as Hwf. intuition.
    inversion H0; subst; eauto.
  - eapply typing_presup in H as Hwf. intuition.
    destruct H2 as [i]. inversion H1; subst.
    eapply ptt.syntax.def_rule_full.eq_exp_beta_abs with (S := S) (i:=max i i0); eauto.
    eapply wf_typ_cumu_larger with (i:=i0); eauto. lia.
    eapply wf_typ_cumu_larger with (i:=i); eauto. lia.
  - apply typing_pi_inv in H as Hwf. destruct Hwf as [i]. intuition.
    eauto.
  Unshelve. all : eauto.
Qed.

Scheme full_wf_ctx_ind := Induction for def_rule_full.WfCtx Sort Prop 
  with full_eq_ctx_ind := Induction for def_rule_full.EqCtx Sort Prop
  with full_typing_ind := Induction for def_rule_full.Typing Sort Prop
  with full_subst_typing_ind := Induction for def_rule_full.SubstTyping Sort Prop
  with full_eq_exp_ind := Induction for def_rule_full.EqExp Sort Prop 
  with full_eq_subst_ind := Induction for def_rule_full.EqSubst Sort Prop.

Combined Scheme full_wf_ctx_eq_ctx_typing_subst_typing_eq_exp_eq_subst_mutind from full_wf_ctx_ind, full_eq_ctx_ind, full_typing_ind, full_subst_typing_ind, full_eq_exp_ind, full_eq_subst_ind.

#[local] Hint Constructors def_rule_concise.WfCtx def_rule_concise.EqCtx def_rule_concise.Typing def_rule_concise.SubstTyping def_rule_concise.EqExp def_rule_concise.EqSubst : core.

Lemma rule_concise_complete : 
  (forall Γ, (⊢ Γ)%F -> ⊢ Γ) /\
  (forall Γ Δ, (⊢ Γ ≈ Δ)%F -> ⊢ Γ ≈ Δ) /\
  (forall Γ t T, (Γ ⊢ t : T)%F ->  Γ ⊢ t : T) /\
  (forall Γ σ Δ, (Γ ⊢s σ : Δ)%F -> Γ ⊢s σ : Δ ) /\
  (forall Γ t t' T, (Γ ⊢ t ≈ t' : T)%F -> Γ ⊢ t ≈ t' : T ) /\
  (forall Γ σ σ' Δ, (Γ ⊢s σ ≈ σ': Δ)%F -> Γ ⊢s σ ≈ σ' : Δ ).
Proof.
  apply full_wf_ctx_eq_ctx_typing_subst_typing_eq_exp_eq_subst_mutind; eauto.
Qed.