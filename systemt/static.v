Inductive typ : Prop :=
  | typ_nat : typ
  | typ_arr : typ -> typ -> typ.

Inductive esubst : Prop :=
  | es_shift 
  | es_id 
  | es_comp (σ1 σ2 : esubst)
  | es_ext (σ : esubst) (e : exp) 
with exp : Prop :=
  | exp_var (n : nat)
  | exp_zero  
  | exp_suc (e : exp)
  | exp_rec (T : typ) (z s t: exp)
  | exp_abs (e : exp)
  | exp_app (e1 e2 : exp)
  | exp_subst (e : exp) (σ : esubst).
 
Definition q (σ : esubst) := es_ext (es_comp σ es_shift) (exp_var 0). 