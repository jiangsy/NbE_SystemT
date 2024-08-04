(* Soundness of the syntactic rules (typing and equality) *)
Require Import nbe.systemt.intensional.totality.

Print Assumptions nbe.systemt.intensional.totality.nbe_totality.

Require Import nbe.systemt.extensional.soundness.
Require Import nbe.systemt.extensional.completeness.

Print Assumptions nbe.systemt.extensional.soundness.nbe_soundness.
Print Assumptions nbe.systemt.extensional.soundness.nbe_totality.
Print Assumptions nbe.systemt.extensional.completeness.nbe_completeness.
Print Assumptions nbe.systemt.extensional.completeness.nbe_totality.
