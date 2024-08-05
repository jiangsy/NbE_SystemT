Require Import Coq.Program.Equality.
Require Import Coq.Lists.List.

Require Import nbe.ptt.syntax.def.

Reserved Notation "⊢ Γ"
  (at level 55, no associativity).
Reserved Notation "Γ ⊢ t : T"
  (at level 55, t at next level, no associativity).
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
where "⊢ Γ" := (WfCtx Γ) and
      "Γ ⊢ t : T" := (Typing Γ t T).