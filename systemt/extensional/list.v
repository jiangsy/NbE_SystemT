Require Import Coq.Lists.List.

Definition one {C : Type} (item : C) : list C := cons item nil.

Section ListProperties.
  Variable X : Type.
  Variables x y : X.
  Variables l l1 l2 l3 : list X.

  Lemma cons_app_one :
    cons x l = one x ++ l.
  Proof.
    clear. auto.
  Qed.

  Lemma cons_app_assoc :
    (cons x l1) ++ l2 = cons x (l1 ++ l2).
  Proof.
    clear. auto.
  Qed.

  Lemma app_assoc :
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    clear. induction l1; auto.
    simpl. rewrite IHl. auto.
  Qed.

  Lemma app_nil_1 :
    nil ++ l = l.
  Proof.
    clear. auto.
  Qed.

  Lemma app_nil_2 :
    l ++ nil = l.
  Proof.
    clear. induction l; auto. simpl.
    rewrite IHl0. auto.
  Qed.

End ListProperties.

#[export] Hint Rewrite cons_app_one cons_app_assoc      : rewr_list.
#[export] Hint Rewrite app_assoc app_nil_1 app_nil_2    : rewr_list.

Ltac simpl_alist :=
  autorewrite with rewr_list.
Tactic Notation "simpl_alist" "in" hyp(H) :=
  autorewrite with rewr_list in H.
Tactic Notation "simpl_alist" "in" "*" :=
  autorewrite with rewr_list in *.