(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*      Coq V5.8                                                            *)
(*                                                                          *)
(*                                                                          *)
(*      First-order Unification                                             *)
(*                                                                          *)
(*      Joseph Rouyer                                                       *)
(*                                                                          *)
(*      November 1992                                                       *)
(*                                                                          *)
(****************************************************************************)
(*                             listv_is_in_lv.v                             *)
(****************************************************************************)

Require Import Arith.
Require Import nat_complements.
Require Import nat_term_eq_quasiterm.
Require Import is_in_quasiterm_term_subst.

(***********************************************************************)
(*********************** Lists of variables : *****************************)
(***********************************************************************)

Inductive listv : Set :=
  | Nilv : listv
  | Consv : var -> listv -> listv.

Definition BNilv (l : listv) : Prop :=
  match l return Prop with
  | Nilv => True
  | Consv x l => False
  end.

Definition BConsv (l : listv) : Prop :=
  match l return Prop with
  | Nilv => False
  | Consv x l => True
  end.

Fixpoint Appv (l0 : listv) : listv -> listv :=
  fun l1 : listv =>
  match l0 return listv with
  | Nilv => l1
  | Consv x l2 => Consv x (Appv l2 l1)
  end.

Definition Headv (x : var) (l : listv) : var :=
  match l return var with
  | Nilv => x
  | Consv y _ => y
  end.

Definition Tailv (l : listv) : listv :=
  match l return listv with
  | Nilv => Nilv
  | Consv _ l1 => l1
  end.

(***********************************************************************)
(**************** Predicate "to be member of a list" : *********************)
(***********************************************************************)

Inductive is_in_lv (x : var) : listv -> Prop :=
  | is_in_lv_init : forall l : listv, is_in_lv x (Consv x l)
  | is_in_lv_Consv :
      forall (l : listv) (x0 : var), is_in_lv x l -> is_in_lv x (Consv x0 l).

Fixpoint IS_IN_LV (x : var) (l : listv) {struct l} : Prop :=
  match l return Prop with
  | Nilv => False
  | Consv y l2 => IS_IN_LV x l2 \/ x = y :>var
  end.

Lemma is_in_lv_IS_IN_LV :
 forall (l : listv) (x : var), is_in_lv x l -> IS_IN_LV x l.
intros; elim H; simpl in |- *; auto.
Qed.

Lemma IS_IN_LV_is_in_lv :
 forall (l : listv) (x : var), IS_IN_LV x l -> is_in_lv x l.
simple induction l; simpl in |- *; intros.
elim H.
elim H0; intros.
apply is_in_lv_Consv; auto.
elim H1; apply is_in_lv_init; auto.
Qed.

(***********************************************************************)
(************ Properties 1) if x belongs to l and is not the head, ***********)
(************************* then x belongs to the tail. *********************)
(***********************************************************************)

Lemma IS_IN_LV_n_eq :
 forall (x x0 : var) (l : listv),
 IS_IN_LV x (Consv x0 l) -> x <> x0 :>var -> IS_IN_LV x l.
simple induction l; simpl in |- *; intros.
elim H; intros; auto; elim H0; auto.
elim H0; intros; auto.
Qed.

(***********************************************************************)
(********************** 2) [x0] contains only x0 . ************************)
(***********************************************************************)

Lemma IS_IN_LV_Consv_Nilv_eq :
 forall x x0 : var, IS_IN_LV x (Consv x0 Nilv) -> x = x0 :>var.
intros; elim H; intros h; elim h; auto.
Qed.

(***********************************************************************)
(********************** 3) Decidability of IS_IN_LV : *********************)
(***********************************************************************)

Lemma IS_IN_LV_decS :
 forall (x : var) (l : listv), {IS_IN_LV x l} + {~ IS_IN_LV x l}.
simple induction l; simpl in |- *; intros.
(*l=Nilv*)
auto.
(*l=(Consv v y)*)
elim H; intros.
auto.
elim (var_eq_decS x v); intros.
(* ... <var>x=v *)
auto.
(*... ~<var>x=v*)
right; tauto.
Qed.

Lemma IS_IN_LV_decP :
 forall (x : var) (l : listv), IS_IN_LV x l \/ ~ IS_IN_LV x l.
intros; elim (IS_IN_LV_decS x l); intros; auto.
Qed.

(***********************************************************************)
(*********************** IS_IN_LV and Appv *****************************)
(***********************************************************************)

Lemma IS_IN_LV_Appv1 :
 forall (l l0 : listv) (x : var), IS_IN_LV x l -> IS_IN_LV x (Appv l l0).
simple induction l; simpl in |- *; intros.
elim H; auto.
elim H0; intros; auto.
Qed.

Lemma IS_IN_LV_Appv2 :
 forall (l l0 : listv) (x : var), IS_IN_LV x l0 -> IS_IN_LV x (Appv l l0).
intros l; elim l; simpl in |- *; auto.
Qed.

Lemma IS_IN_LV_Appv_IS_IN_LV :
 forall (l l0 : listv) (x : var),
 IS_IN_LV x (Appv l l0) -> IS_IN_LV x l \/ IS_IN_LV x l0.
simple induction l; simpl in |- *; intros; auto.
elim H0; intros; auto.
elim (H l1 x); auto.
Qed.

(***********************************************************************)
