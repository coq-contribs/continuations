(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                 The Calculus of Inductive Constructions                  *)
(*                                                                          *)
(*                                Projet Coq                                *)
(*                                                                          *)
(*                     INRIA                        ENS-CNRS                *)
(*              Rocquencourt                        Lyon                    *)
(*                                                                          *)
(*                                Coq V5.10                                 *)
(*                              Nov 25th 1994                               *)
(*                                                                          *)
(****************************************************************************)
(*                               term_unif.v                                *)
(****************************************************************************)

Require Import Arith.
Require Import nat_complements.
Require Import nat_term_eq_quasiterm.
Require Import is_in_quasiterm_term_subst.
Require Import listv_is_in_lv.


(***********************************************************************)
(** Predicates that count the different elements of a list: ********************)
(**** diffelnb is an inductive definition  ***********************************)
(**** The definition of DIFFELNB is recursive. ****************************)
(***********************************************************************)

Inductive diffelnb : listv -> nat -> Prop :=
  | diffelnb_init : diffelnb Nilv 0
  | diffelnb_Consv_in :
      forall (l : listv) (n : nat) (x : var),
      diffelnb l n -> IS_IN_LV x l -> diffelnb (Consv x l) n
  | diffelnb_Consv_n_in :
      forall (l : listv) (n : nat) (x : var),
      diffelnb l n -> ~ IS_IN_LV x l -> diffelnb (Consv x l) (S n).

Fixpoint DIFFELNB (l : listv) : nat -> Prop :=
  match l return (nat -> Prop) with
  | Nilv => fun x : nat => 0 = x :>nat
  | Consv y l1 =>
      fun n : nat =>
      match n return Prop with
      | O => False
      | S p =>
          IS_IN_LV y l1 /\ DIFFELNB l1 (S p) \/
          ~ IS_IN_LV y l1 /\ DIFFELNB l1 p
      end
  end.


(***********************************************************************)
(**************** DIFFELNB is equivalent to diffelnb *********************)
(***********************************************************************)

Lemma diffelnb_DIFFELNB :
 forall (l : listv) (n : nat), diffelnb l n -> DIFFELNB l n.
intros; elim H; simpl in |- *; auto with arith.
intros l0 n0; elim n0; simpl in |- *; auto with arith.
elim l0; simpl in |- *; auto with arith.
Qed.

Lemma DIFFELNB_diffelnb :
 forall (l : listv) (n : nat), DIFFELNB l n -> diffelnb l n.
simple induction l.
simple induction n; simpl in |- *; intros.
exact diffelnb_init.
discriminate H0.
simple induction n; intros.
elim H0.                            (*(DIFFELNB (Consv v y) O):False*)
elim H1; intros h; elim h; intros.
apply diffelnb_Consv_in; auto with arith.
apply diffelnb_Consv_n_in; auto with arith.
Qed.

(***********************************************************************)
(****************** Existence of an integer that counts ******************)
(***********************************************************************)

Lemma DIFFELNBor : forall l : listv, {count : nat | DIFFELNB l count}.
simple induction l.
exists 0; simpl in |- *; auto with arith.  (*case l=Nilv*)
intros v y H.               (*case l=(Consv v y)*)
elim H; intros.
elim (IS_IN_LV_decS v y); intros.
exists x.             (*case v in y:(IS_IN_LV v y)*)
cut (DIFFELNB y x); auto with arith.
elim x; simpl in |- *; auto with arith.    (*case x=(S p)*)
cut (IS_IN_LV v y); auto with arith. (*case x=O*)
elim y; simpl in |- *; auto with arith.    (*case v not in y:~(IS_IN_LV v y)*)
exists (S x); simpl in |- *; auto with arith.
Qed.

(***********************************************************************)
(******** The empty list is the only list that contains 0 element. ************)
(***********************************************************************)

Lemma DIFFELNB_O : forall l : listv, DIFFELNB l 0 -> Nilv = l :>listv.
simple induction l; simpl in |- *; auto with arith.
intros; absurd False; auto with arith.
Qed.

Lemma DIFFELNB_Consv_n_O :
 forall (l : listv) (n : nat) (x : var),
 DIFFELNB (Consv x l) n -> 0 <> n :>nat.
simple induction n.
simpl in |- *; tauto.
intros; discriminate.
Qed.

(*******************************************************************)
(********* Inclusion and strict inclusion for the lists as sets. ***********)
(*******************************************************************)

Inductive inclv (l1 l2 : listv) : Prop :=
    inclv_init :
      (forall y : var, IS_IN_LV y l1 -> IS_IN_LV y l2) -> inclv l1 l2.

Inductive st_inclv (l1 l2 : listv) : Prop :=
    st_inclv_init :
      forall x : var,
      ~ IS_IN_LV x l1 ->
      IS_IN_LV x l2 ->
      (forall y : var, IS_IN_LV y l1 -> IS_IN_LV y l2) -> st_inclv l1 l2.

Lemma n_st_inclv_l_Nilv : forall l : listv, ~ st_inclv l Nilv.
intros l; unfold not in |- *; intros h; elim h; auto with arith.
Qed.

(*******************************************************************)
(*************************** Remove : ******************************)
(**************** remove is inductively defined, ***********************)
(**************** REMOVE is recursively defined. *********************)
(*******************************************************************)

Inductive remove (x : var) : listv -> listv -> Prop :=
  | remove_init : remove x Nilv Nilv
  | remove_eq : forall l l0 : listv, remove x l l0 -> remove x (Consv x l) l0
  | remove_n_eq :
      forall (l l0 : listv) (x0 : var),
      remove x l l0 -> x <> x0 :>var -> remove x (Consv x0 l) (Consv x0 l0).

Fixpoint REMOVE (x : var) (l : listv) {struct l} : 
 listv -> Prop :=
  match l return (listv -> Prop) with
  | Nilv => fun l1 : listv => Nilv = l1 :>listv
  | Consv v l1 =>
      fun l2 : listv =>
      x = v :>var /\ REMOVE x l1 l2 \/
      x <> v :>var /\
      match l2 return Prop with
      | Nilv => False
      | Consv w l3 => v = w :>var /\ REMOVE x l1 l3
      end
  end.

(*******************************************************************)
(************** REMOVE is equivalent to remove *********************)
(*******************************************************************)

Lemma remove_REMOVE :
 forall (l l0 : listv) (x : var), remove x l l0 -> REMOVE x l l0.
intros; elim H; intros; simpl in |- *; auto with arith.
Qed.

Lemma REMOVE_remove :
 forall (l l0 : listv) (x : var), REMOVE x l l0 -> remove x l l0.
simple induction l.
intros; elim H; apply remove_init.
simple induction l1.
simpl in |- *; intros.
elim H0; intros h1; elim h1; intros.
elim H1; apply remove_eq; auto with arith.
absurd False; auto with arith.
intros.
elim H1; intros.
elim H2; intros h h0; elim h; apply remove_eq; auto with arith.
elim H2; intros h h0; elim h0; intros h1 h2; elim h1; apply remove_n_eq;
 auto with arith.
Qed.

(*******************************************************************)
(******************** REMOVE and not IS_IN_LV ********************)
(*******************************************************************)

Lemma REMOVE_n_IS_IN_LV_eq :
 forall (l l0 : listv) (x : var),
 REMOVE x l l0 -> ~ IS_IN_LV x l -> l = l0 :>listv.
intros l l0 x h; cut (remove x l l0).
2: apply REMOVE_remove; auto with arith.
intros h0; elim h0; auto with arith.
intros; elim H1; simpl in |- *; auto with arith.
simpl in |- *; intros.
elim H0; auto with arith; unfold not in |- *; intros; elim H2; auto with arith.
Qed.


(*******************************************************************)
(********************** REMOVE and Consv ************************)
(*******************************************************************)

Lemma REMOVE_Consv_eq :
 forall (l l0 : listv) (x : var), REMOVE x (Consv x l) l0 -> REMOVE x l l0.
intros until x; simpl in |- *; intros.
elim H; intros h; elim h; intros; auto with arith.
absurd (x = x :>var); auto with arith.
Qed.

Lemma REMOVE_Consv_n_eq :
 forall (l l0 : listv) (x x0 : var),
 REMOVE x (Consv x0 l) (Consv x0 l0) -> x0 <> x :>var -> REMOVE x l l0.
intros l l0 x x0; simpl in |- *; intros; auto with arith.
elim H; intros h; elim h; intros.
absurd (x0 = x :>var); auto with arith.
elim H2; auto with arith.
Qed.

(*******************************************************************)
(************** Existence of an l0 such that (REMOVE l l0) ***********)
(*******************************************************************)

Lemma sig_REMOVE : forall (l : listv) (x : var), {l0 : listv | REMOVE x l l0}.
simple induction l; intros.
exists Nilv; simpl in |- *; auto with arith.
elim (H x); intros l1 h.
elim (var_eq_decS x v); intros h0.
elim h0; exists l1; simpl in |- *.
intuition.
exists (Consv v l1); simpl in |- *.
intuition.
Qed.

Lemma exi_REMOVE :
 forall (l : listv) (x : var), exists l0 : listv, REMOVE x l l0.
intros; elim (sig_REMOVE l x); intros l0 h; exists l0; auto with arith.
Qed.

(*******************************************************************)
(************************ Properties of REMOVE ********************)
(*******************************************************************)

Lemma Headv_REMOVE_Consv_Nilv :
 forall (l l0 : listv) (x x0 : var),
 REMOVE x (Consv x0 l) l0 -> x <> x0 :>var -> Nilv <> l0 :>listv.
simple induction l0; intros.
elim H; intros h; elim h; intros.
absurd (x = x0 :>var); auto with arith.
absurd False; auto with arith.
apply Diff with BNilv; auto with arith; simpl in |- *; auto with arith.
Qed.

Lemma REMOVE_Consv_n_eq_Headv :
 forall (l l0 : listv) (x x0 : var),
 REMOVE x (Consv x0 l) l0 ->
 x <> x0 :>var -> Nilv <> l0 :>listv /\ x0 = Headv x l0 :>var.
intros; split.
apply Headv_REMOVE_Consv_Nilv with l x x0; auto with arith.
cut (REMOVE x (Consv x0 l) l0).
2: auto with arith.
elim l0.
simpl in |- *; intros h; elim h.
intros h0; elim h0; auto with arith.
intros h0; elim h0; intros; absurd False; auto with arith.
intros; simpl in |- *.
elim H2; intros.
elim H3; intros.
absurd (x = x0 :>var); auto with arith.
elim H3; intros h1 h2; elim h2; auto with arith.
Qed.

(*******************************************************************)
(*********** Properties linked to REMOVE and IS_IN_LV ***************)
(*******************************************************************)

Lemma REMOVE_IS_IN_LV_IS_IN_LV :
 forall (l l0 : listv) (x x0 : var),
 REMOVE x l l0 -> IS_IN_LV x0 l0 -> IS_IN_LV x0 l.
intros l l0 x x0 h; cut (remove x l l0).
2: apply REMOVE_remove; auto with arith.
intro; elim H; simpl in |- *; auto with arith.
intros.
elim H3; intros; auto with arith.
Qed.

Lemma REMOVE_n_eq_IS_IN_LV_IS_IN_LV :
 forall (l l0 : listv) (x : var),
 REMOVE x l l0 ->
 forall x0 : var, x <> x0 :>var -> IS_IN_LV x0 l -> IS_IN_LV x0 l0.
intros l l0 x H; cut (remove x l l0).
2: apply REMOVE_remove; auto with arith.
intro; elim H0; simpl in |- *; auto with arith.
intros.
elim H4; auto with arith.
intros; absurd (x = x0 :>var); auto with arith.
intros.
elim H5; auto with arith.
Qed.

(**********************************************************************)
(************************* REMOVE and st_inclv : **********************) 
(*********************** if x does not belong to l ************************)
(******* and x belongs to l0 and l st_inclv l0, and (REMOVE x l0 l1) ******)
(************************** then l st_inclv l1. ***************************)
(**********************************************************************)

Lemma st_inclv_Consv_REMOVE_n_IS_IN_LV_st_inclv :
 forall (l l0 l1 : listv) (x : var),
 st_inclv (Consv x l) l0 -> REMOVE x l0 l1 -> ~ IS_IN_LV x l -> st_inclv l l1.
intros l l0 l1 x h; elim h.
simpl in |- *; intros.
apply st_inclv_init with x0.
unfold not in |- *; intros; apply H; auto with arith.
cut (x0 <> x :>var).
intros; apply (REMOVE_n_eq_IS_IN_LV_IS_IN_LV l0 l1 x); auto with arith.
unfold not in |- *; intros; elim H4; auto with arith.
(*unfold not;intros;apply H;auto with arith.*)
intros; cut (x <> y :>var).
intros; apply (REMOVE_n_eq_IS_IN_LV_IS_IN_LV l0 l1 x); auto with arith.
unfold not in |- *; intros; apply H3; replace x with y; auto with arith.
Qed.

(**********************************************************************)
(*********************** REMOVE and DIFFELNB **********************)
(**********************************************************************)

Lemma REMOVE_n_IS_IN_LV_DIFFELNB_pred :
 forall (l : listv) (n : nat),
 DIFFELNB l n ->
 forall (l0 : listv) (x : var),
 REMOVE x l l0 -> IS_IN_LV x l -> DIFFELNB l0 (pred n).
intros l n h; cut (diffelnb l n).
2: apply DIFFELNB_diffelnb; auto with arith.
intros H; elim H.
(* Case1 :  l=Nilv *)
simpl in |- *; tauto.
(* Case2 l=(Consv x l0) and (IS_IN_LV x l0) *)
intros until x0; elim (var_eq_decP x x0); intro.
(* Case2 ... H3:<var>x=x0*)
elim H3; intros.
apply H1 with x; auto with arith.
apply REMOVE_Consv_eq; auto with arith.
(* Case2 ... H3:~<var>x=x0*)
elim l1.
(* Case2 ... H3:~<var>x=x0;l1=Nilv**)
simpl in |- *; intros.
elimtype False; intuition.
(* Case2 ... H3:~<var>x=x0;l1=(Consv v y)*)
intros v y h0 h1; elim h1; intros.
elim H4; intros; absurd (x = x0 :>var); auto with arith.
elim H4; intros h2 h3; elim h3; intros h4 h5; elim h4.
apply diffelnb_DIFFELNB; apply diffelnb_Consv_in.
apply DIFFELNB_diffelnb; apply (H1 y x0); auto with arith.
elim H5; intros; auto with arith; absurd (x = x0 :>var); auto with arith.
apply REMOVE_n_eq_IS_IN_LV_IS_IN_LV with l0 x0; auto with arith.

(* Case3 l=(Consv x l0) and ~(IS_IN_LV x l0) *) 
intros l0 n0 x H0 H1 H2 l1; elim l1.
(* Case3 ...l1=Nilv*)
intros x0 H3 H4.
elim H3; intros h0; elim h0; intros.
cut (~ IS_IN_LV x l0).
2: auto with arith.
elim H5; intros; cut (l0 = Nilv :>listv).
2: apply REMOVE_n_IS_IN_LV_eq with x0; auto with arith.
intros; cut (DIFFELNB l0 n0).
2: apply diffelnb_DIFFELNB; auto with arith; replace l0 with Nilv;
    simpl in |- *; auto with arith.
elim H8; simpl in |- *; auto with arith.
elim H6.
(*Case3 ...l1=(Consv v l2)*)
intros v l2 H3 x0 H4 H5.
change (DIFFELNB (Consv v l2) n0) in |- *.
elim H4; intros.
(*Case3 ...l1=(Consv v l2))and (<var>x0=x) *)
(*           and (REMOVE x0 l0 (Consv v l2))*)
elim H6; intros.
cut (DIFFELNB l0 n0).
2: apply diffelnb_DIFFELNB; auto with arith.
cut (~ IS_IN_LV x l0).
2: auto with arith.
elim H7; intros; replace (Consv v l2) with l0;
 try apply REMOVE_n_IS_IN_LV_eq with x0; auto with arith.
(*Case3 ...l1=(Consv v y))and ~<var>x0=x*)
(*                         and <var>x=v) and (REMOVE x0 l0 y) *)
elim H6; intros h0 h1; elim h1; intros.
elim H5; intros.
cut (DIFFELNB l2 (pred n0)).
2: apply (H1 l2 x0); auto with arith.
cut (DIFFELNB l0 n0).
2: apply diffelnb_DIFFELNB; auto with arith.
pattern n0 in |- *; apply (nat_case n0).
simpl in |- *; intros; absurd (IS_IN_LV x0 l0); auto with arith.
replace l0 with Nilv; try apply DIFFELNB_O; auto with arith.
simpl in |- *; intros.
elim H7; right; split; auto with arith.
unfold not in |- *; intros; elim H2;
 apply (REMOVE_IS_IN_LV_IS_IN_LV l0 l2 x0); auto with arith.
absurd (x0 = x :>var); auto with arith.
Qed.

(**********************************************************************)
(************************* st_inclv and DIFFELNB **********************)
(**********************************************************************)

Lemma DIFFELNB_st_inclv_le_S :
 forall (l : listv) (n : nat),
 DIFFELNB l n ->
 forall (l0 : listv) (n0 : nat), DIFFELNB l0 n0 -> st_inclv l l0 -> S n <= n0.
intros l n hyp; cut (diffelnb l n).
2: apply DIFFELNB_diffelnb; auto with arith.
intros h; elim h.
(* Case1 :  l=Nilv *)
intros l0 n0; pattern n0 in |- *; apply (nat_case n0).
simpl in |- *; intros.
elim H0; intros; cut (DIFFELNB l0 0); auto with arith.
intros; absurd (IS_IN_LV x l0); auto with arith.
cut (Nilv = l0 :>listv).
intros H5; elim H5; simpl in |- *; auto with arith.
apply DIFFELNB_O; auto with arith.
intros; auto with arith.
(* Case2 l=(Consv x l0) and (IS_IN_LV x l0) *)
intros until n1; pattern n1 in |- *; apply (nat_case n1).
intros h0 h1; elim h1; intros.
absurd (IS_IN_LV x0 l1); auto with arith.
cut (Nilv = l1 :>listv).
intros H5; elim H5; simpl in |- *; auto with arith.
apply DIFFELNB_O; auto with arith.
intros; apply (H0 l1 (S m)); auto with arith.
elim H3; intros.
apply st_inclv_init with x0; auto with arith.
unfold not in |- *; intros; elim H4; simpl in |- *; auto with arith.
intros; apply H6; simpl in |- *; auto with arith.
(* Case3 l=(Consv x l0) and ~(IS_IN_LV x l0) *) 
intros until n1; pattern n1 in |- *; apply (nat_case n1).
intros h0 h1; elim h1; intros.
absurd (IS_IN_LV x0 l1); auto with arith.
cut (Nilv = l1 :>listv).
intros H5; elim H5; simpl in |- *; auto with arith.
apply DIFFELNB_O; auto with arith.
intros; apply le_n_S.
elim (exi_REMOVE l1 x); intros l2 H5.
apply (H0 l2).
replace m with (pred (S m));
 try apply REMOVE_n_IS_IN_LV_DIFFELNB_pred with l1 x; 
 auto with arith.
elim H3; intros.
apply (H7 x); simpl in |- *; auto with arith.
apply st_inclv_Consv_REMOVE_n_IS_IN_LV_st_inclv with l1 x; auto with arith.
Qed.

(**********************************************************************)
(************************* inclv and DIFFELNB ************************)
(**********************************************************************)

Lemma inclv_le :
 forall (l : listv) (n : nat),
 DIFFELNB l n ->
 forall (l0 : listv) (n0 : nat), DIFFELNB l0 n0 -> inclv l l0 -> n <= n0.
intros l n hyp; cut (diffelnb l n).
2: apply DIFFELNB_diffelnb; auto with arith.
intros h; elim h.
(* Case1 :  l=Nilv *)
auto with arith. (*apply le_O_n*)
(* Case2 l=(Consv x l0) and (IS_IN_LV x l0) *)
intros.
apply H0 with l1; auto with arith.
apply inclv_init; intros; elim H3; simpl in |- *; auto with arith.
(* Case3 l=(Consv x l0) and ~(IS_IN_LV x l0) *) 
intros until n1; pattern n1 in |- *; apply (nat_case n1).
intros; absurd (IS_IN_LV x l1).
cut (Nilv = l1 :>listv).
2: apply DIFFELNB_O; auto with arith.
intros H4; elim H4; simpl in |- *; auto with arith.
elim H3; simpl in |- *; auto with arith.
intros; elim (exi_REMOVE l1 x); intros.
apply le_n_S; apply H0 with x0.
replace m with (pred (S m)); auto with arith.
apply REMOVE_n_IS_IN_LV_DIFFELNB_pred with l1 x; auto with arith.
elim H3; simpl in |- *; auto with arith.
apply inclv_init; intros.
apply REMOVE_n_eq_IS_IN_LV_IS_IN_LV with l1 x; auto with arith.
unfold not in |- *; intros h0; absurd (IS_IN_LV y l0); auto with arith; elim h0;
 auto with arith.
elim H3; simpl in |- *; auto with arith.
Qed.

(*******************************************************************)
(********************* (infv t u) is true  ****************************)
(********* if every variable of t is a variable of u and *****************)
(***** if there exists a variable of u which is not a variable of t. ********)
(************ One reads t is less than u by its variables. ***************)
(*******************************************************************)

Inductive infv (t1 t2 : quasiterm) : Prop :=
    infv_init :
      forall x : var,
      ~ IS_IN x t1 ->
      IS_IN x t2 -> (forall y : var, IS_IN y t1 -> IS_IN y t2) -> infv t1 t2.

(*******************************************************************)
(********** A closed quasiterm has no variable ***********************)
(*******************************************************************)

Inductive clos (t : quasiterm) : Prop :=
    clos_init : (forall x : var, ~ IS_IN x t) -> clos t.

(*******************************************************************)
(*********** The list of the variables that occur in a quasiterm *********)
(*******************************************************************)

Fixpoint list_var (t : quasiterm) : listv :=
  match t return listv with
  | V x => Consv x Nilv
  | C l => Nilv
  | Root l t0 => list_var t0
  | ConsArg t1 t2 => Appv (list_var t1) (list_var t2)
  end.

(*******************************************************************)
(********** (IS_IN x t) and (IS_IN_LV x (list_var t)) are equivalent. *****)
(*******************************************************************)

Goal forall (t : quasiterm) (x : var), IS_IN x t -> IS_IN_LV x (list_var t).
simple induction t; simpl in |- *; intros; auto with arith.
(*Case t=(V v) : apply or_is_inror ; assumption
Case t=(C c) : assumption
Case t=(Root f y) : apply H ; assumption *)
(*Case t=(ConsArg y y0) *) 
elim H1; intros.
apply IS_IN_LV_Appv1; auto with arith.
apply IS_IN_LV_Appv2; auto with arith.
Save IS_IN_IS_IN_LV.

Goal forall (t : quasiterm) (x : var), IS_IN_LV x (list_var t) -> IS_IN x t.
simple induction t; simpl in |- *; auto with arith.
tauto.
(*Case t=(ConsArg y y0) *)
intros q H q0 H0 x H1;
 elim (IS_IN_LV_Appv_IS_IN_LV (list_var q) (list_var q0) x H1); 
 intros; auto with arith.
Save IS_IN_LV_IS_IN.

(**********************************************************************)
(********** To count the different variables of a quasiterm  *****************)
(**********************************************************************)
Goal forall t : quasiterm, DIFFELNB (list_var t) 0 -> clos t.
intros; apply clos_init.
unfold not in |- *; intros x h; absurd (IS_IN_LV x (list_var t)).
replace (list_var t) with Nilv; try apply (DIFFELNB_O (list_var t));
 auto with arith.
apply IS_IN_IS_IN_LV; auto with arith.
Save DIFFELNB_O_clos.

(**********************************************************************)
(********************** clos and ConsArg. ******************************)
(**********************************************************************)

Goal forall t1 t2 : quasiterm, clos (ConsArg t1 t2) -> clos t1.
intros; elim H; intros; apply clos_init.
intros x; unfold not in |- *; intros; elim (H0 x); simpl in |- *;
 auto with arith.
Save closConsArg1.

Goal forall t1 t2 : quasiterm, clos (ConsArg t1 t2) -> clos t2.
intros; elim H; intros; apply clos_init.
intros x; unfold not in |- *; intros; elim (H0 x); simpl in |- *;
 auto with arith.
Save closConsArg2.

Goal forall t1 t2 : quasiterm, clos (ConsArg t1 t2) -> clos t1 /\ clos t2.
intros; elim H; intros; split; apply clos_init.
intros x; unfold not in |- *; intros; elim (H0 x); simpl in |- *;
 auto with arith.
intros x; unfold not in |- *; intros; elim (H0 x); simpl in |- *;
 auto with arith.
Save closConsArg.

Goal forall (f : fun_) (y : quasiterm), clos (Root f y) -> clos y.
intros.
elim H.
intros.
apply clos_init.
intros.
generalize (H0 x).
simpl in |- *; auto with arith.
Save closRoot.

Goal forall t : quasiterm, clos t -> DIFFELNB (list_var t) 0.
simple induction t.
(*Case t=(V v) *)
intros; elim H.
simpl in |- *; intros; absurd (v = v :>var); auto with arith.
(*Case t=(C c) *)
intros; simpl in |- *; auto with arith.
(*Case t=(Root f y) *)
intros; simpl in |- *; apply H; generalize (closRoot _ _ H0);
 auto with arith.
(*Case t=(ConsArg y y0) *)
simpl in |- *; intros q H q0 H0 H1.
elim (closConsArg q q0 H1); intros.
replace (list_var q) with Nilv; try apply DIFFELNB_O; auto with arith.
Save clos_DIFFELNBO.

Goal
forall t0 t1 : quasiterm, infv t0 t1 -> st_inclv (list_var t0) (list_var t1).
intros; elim H; intros.
apply st_inclv_init with x.
unfold not in |- *; intros; elim H0; apply IS_IN_LV_IS_IN; auto with arith.
apply IS_IN_IS_IN_LV; auto with arith.
intros; apply IS_IN_IS_IN_LV; apply H2; apply IS_IN_LV_IS_IN; auto with arith. 
Save infv_st_inclv.

Goal
forall t0 t1 : quasiterm, st_inclv (list_var t0) (list_var t1) -> infv t0 t1.
intros; elim H; intros.
apply infv_init with x.
unfold not in |- *; intros; elim H0; apply IS_IN_IS_IN_LV; auto with arith.
apply IS_IN_LV_IS_IN; auto with arith.
intros; apply IS_IN_LV_IS_IN; apply H2; apply IS_IN_IS_IN_LV; auto with arith. 
Save st_inclv_infv.

Goal forall t : quasiterm, clos t -> forall t0 : quasiterm, ~ infv t0 t.
unfold not in |- *; intros.
elim H; intros.
elim H0; intros.
elim (H1 x); auto with arith.
Save n_infv_t_clos.

(**********************************************************************)
(*************** Quasisubstitution extensively equal to V ******************)
(**********************************************************************)

Goal
forall (f : quasisubst) (t : quasiterm),
(forall x : var, V x = f x :>quasiterm) -> t = Subst f t :>quasiterm.
simple induction t; simpl in |- *; auto with arith; intros.
elim H; auto with arith.
elim H; elim H0; auto with arith.
Save eq_V_stab.

Goal forall t : quasiterm, t = Subst V t :>quasiterm.
intros; apply eq_V_stab; auto with arith.
Save V_stab.

Goal
forall (t : quasiterm) (f : quasisubst), clos t -> t = Subst f t :>quasiterm.
intros; elim H; intros.
apply trans_equal with (Subst V t); try apply V_stab.
apply eq_restriction_s_t; intros; absurd (IS_IN x t); auto with arith.
Save clossubst.

(**********************************************************************)
(***************** Predicate dom : (dom f x) is true *********************)
(******************** if f(x) is not equal to V(x). ***********************)
(**********************************************************************)

Definition dom (f : quasisubst) (x : var) : Prop := V x <> f x :>quasiterm.

Goal forall (f : quasisubst) (x : var), ~ dom f x -> V x = f x :>quasiterm.
intros f x; elim (quasiterm_eq_decP (V x) (f x)); intros; auto with arith.
elim H0; auto with arith.
Save n_dom.

Goal forall (f : quasisubst) (x : var), dom f x \/ ~ dom f x.
intros f x; elim (quasiterm_eq_decP (V x) (f x)); intros; auto with arith.
Save dom_decP.

(**********************************************************************)
(***************** Predicate range : (range f x) is true *******************)
(***************** if the variable x is in the image **********************)
(***************** of an other variable under f. *************************)
(**********************************************************************)

Inductive range (s : quasisubst) (x : var) : Prop :=
    range_init : forall y : var, dom s y -> IS_IN x (s y) -> range s x.

Goal
forall (f : quasisubst) (x : var),
~ range f x -> forall y : var, dom f y -> ~ IS_IN x (f y).
unfold not in |- *; intros.
elim H; apply range_init with y; auto with arith.
Save n_range_n_IS_IN.

Goal
forall (f : quasisubst) (x y : var),
~ range f x -> IS_IN x (f y) -> x = y :>var.
intros.
elim (dom_decP f y); intros h.
(*Case (dom f y) *)
absurd (IS_IN x (f y)); auto with arith.
unfold not in |- *; intros; elim H; intros.
apply range_init with y; auto with arith.
(*Case ~(dom f y) *)
change (IS_IN x (V y)) in |- *.
replace (V y) with (f y); auto with arith.
elim (n_dom f y); auto with arith.
Save n_range_IS_IN_eq.

Goal
forall (f : quasisubst) (t : quasiterm) (x : var),
~ range f x -> IS_IN x (Subst f t) -> IS_IN x t.
simple induction t; simpl in |- *; intros; auto with arith.
simpl in |- *; intros; apply n_range_IS_IN_eq with f; auto with arith.
elim H2; intros; auto with arith.
Save n_range_IS_IN_Subst.

(**********************************************************************)
(***************** Predicate over : (over f t) is true *********************)
(***************** if f does not modify the variables *********************)
(***************** which are not in t. **********************************)
(**********************************************************************)

Definition over (f : quasisubst) (t : quasiterm) : Prop :=
  forall x : var, ~ IS_IN x t -> V x = f x :>quasiterm.

(**********************************************************************)
(***************** Predicate under : (under f t) is true ******************)
(***************** if every variable which is in the image ****************)
(***************** of an other variable under f is in t. ******************)
(**********************************************************************)

Definition under (s : quasisubst) (t : quasiterm) : Prop :=
  forall x y : var, dom s y -> IS_IN x (s y) -> IS_IN x t.

(**********************************************************************)
(***************** If (under f t) is true then ****************************)
(***************** every variable which is in the *************************)
(***************** image of t under the quasisubstitution f ****************)
(***************** was before in t. *************************************)
(**********************************************************************)

Goal
forall (f : quasisubst) (t : quasiterm) (x : var),
IS_IN x (Subst f t) -> exists y : var, IS_IN y t /\ IS_IN x (f y).
simple induction t; simpl in |- *; intros; auto with arith. (*Case t=(Root f u) *)
(*Case t=(V v) *)
exists v; auto with arith.
(*Case t=(C c) *)
elim H.
(*Case t=(ConsArg y y0) *)
elim H1; intros.
elim H with x; intros; auto with arith.
elim H3; intros; exists x0; auto with arith.
elim H0 with x; intros; auto with arith.
elim H3; intros; exists x0; auto with arith.
Save IS_IN_Subst_exi_IS_IN.

Goal
forall (f : quasisubst) (t : quasiterm),
under f t -> forall x : var, IS_IN x (Subst f t) -> IS_IN x t.
unfold under in |- *; intros.
elim (IS_IN_Subst_exi_IS_IN f t x H0); intros x0 h; elim h; intros.
elim (var_eq_decP x0 x); intros h0.
elim h0; auto with arith.
apply (H x x0); auto with arith.
unfold dom in |- *; unfold not in |- *; intros.
elim h0; symmetry  in |- *; change (IS_IN x (V x0)) in |- *.
replace (V x0) with (f x0); auto with arith.
Save under_IS_IN_Subst_IS_IN.

(**********************************************************************)
(***************** Strict order sub_term *********************************)
(***************** (usual sense). ***************************************)
(**********************************************************************)

Inductive sub (u : quasiterm) : quasiterm -> Prop :=
  | subConsArgl : forall t : quasiterm, sub u (ConsArg u t)
  | subConsArgr : forall t : quasiterm, sub u (ConsArg t u)
  | subRoot : forall l : fun_, sub u (Root l u)
  | subConsArgl2 : forall t v : quasiterm, sub u t -> sub u (ConsArg t v)
  | subConsArgr2 : forall t v : quasiterm, sub u t -> sub u (ConsArg v t)
  | subRoot2 : forall (t : quasiterm) (l : fun_), sub u t -> sub u (Root l t).

(**********************************************************************)
(***************** Recursive definition : *********************************)
(**********************************************************************)

Fixpoint SUP (t : quasiterm) : quasiterm -> Prop :=
  match t return (quasiterm -> Prop) with
  | V x => fun u : quasiterm => False
  | C l => fun u : quasiterm => False
  | Root l u1 => fun u : quasiterm => u1 = u :>quasiterm \/ SUP u1 u
  | ConsArg u1 u2 =>
      fun u : quasiterm =>
      u1 = u :>quasiterm \/ u2 = u :>quasiterm \/ SUP u1 u \/ SUP u2 u
  end.

Definition SUB (t1 t2 : quasiterm) : Prop := SUP t2 t1.

(**********************************************************************)
(***************** SUB is equivalent to sub *****************************)
(**********************************************************************)

Goal forall t1 t2 : quasiterm, sub t1 t2 -> SUB t1 t2.
intros; elim H; unfold SUB in |- *; simpl in |- *; auto with arith.
Save sub_SUB.

Goal forall t1 t2 : quasiterm, SUB t1 t2 -> sub t1 t2.
simple induction t2; intros.
(*Case t=(V v) *)
elim H.
(*Case t=(C c) *)
elim H.
(*Case t=(Root f y) *)
elim H0; intros.
elim H1; apply subRoot.
apply subRoot2; auto with arith.
(*Case t=(ConsArg y y0) *)
elim H1; intros.
elim H2; apply subConsArgl.
elim H2; intros.
elim H3; apply subConsArgr.
elim H3; intros.
apply subConsArgl2; auto with arith.
apply subConsArgr2; auto with arith.
Save SUB_sub.

(**********************************************************************)
(***************** Transitivity of SUP and SUB : ***********************)
(**********************************************************************)

Goal forall v u w : quasiterm, SUP v u -> SUP w v -> SUP w u.
simple induction v.
intros; absurd False; auto with arith. (*Case v=(V v0) *)
intros; absurd False; auto with arith. (*Case v=(C f) *)
(*Case v=(Root f y)*)
simple induction w.
intros; absurd False; auto with arith. (*Case w=(V v0) *)
intros; absurd False; auto with arith. (*Case w=(C f0) *)
(*Case v=(Root f y);w=(Root f0 y0)*)
intros.
elim H2; intros; elim H1; intros; simpl in |- *; auto with arith.
elim H4; replace q0 with (Root f q); simpl in |- *; auto with arith.
replace q0 with (Root f q); simpl in |- *; auto with arith.
(*Case v=(Root f y);w=(ConsArg y0 y1)*)
intros q0 H0 q1 H1 H2 H3.
elim H3; intro H4.
replace q0 with (Root f q); simpl in |- *; auto with arith.
elim H4; intro H5.
replace q1 with (Root f q); simpl in |- *; auto with arith.
elim H5; intros; simpl in |- *; auto with arith.
(*Case v=(ConsArg y y0)*)
simple induction w.
tauto. (*Case w=(V v0) *)
tauto. (*Case w=(C f0) *)
(*Case v=(ConsArg y y0);w=(Root f0 y0)*)
intros f q1 H1 H2 H3.
elim H3; intros.
replace q1 with (ConsArg q q0); simpl in |- *; auto with arith.
simpl in |- *; auto with arith.
(*Case v=(ConsArg y y0);w=(ConsArg y0 y1)*)
intros q1 H1 q2 H2 H3 H4.
elim H4; intro H5.
elim H3; intro H6.
elim H6; intros; replace q1 with (ConsArg q q0); simpl in |- *; auto with arith.
replace q1 with (ConsArg q q0); simpl in |- *; auto with arith.
elim H5; intro H6.
replace q2 with (ConsArg q q0); simpl in |- *; auto with arith.
elim H6; intros; simpl in |- *; auto with arith.
Save trans_SUP.

Goal forall v u w : quasiterm, SUB u v -> SUB v w -> SUB u w.
unfold SUB in |- *; intros; apply trans_SUP with v; auto with arith.
Save trans_SUB.

Goal forall v u : quasiterm, SUB u v -> u <> v.
intros.
unfold not in |- *; intros h; cut (SUB u v); auto with arith; elim h.
elim u; simpl in |- *; auto with arith. (*Case u=(V v) or u=(C f)*)
(*Case u=(Root f q)*)
intros.
elim H1; intros.
apply H0; pattern q in |- *; replace q with (Root f q); auto with arith.
apply H0; apply trans_SUB with (Root f q); unfold SUB in |- *; simpl in |- *;
 auto with arith.
(*Case u=(ConsArg y y0)*)
intros.
elim H2; intros.
apply H0; pattern q in |- *; replace q with (ConsArg q q0); auto with arith.
elim H3; intros.
apply H1; pattern q0 in |- *; replace q0 with (ConsArg q q0); auto with arith.
elim H4; intros.
apply H0; apply trans_SUB with (ConsArg q q0); unfold SUB in |- *;
 simpl in |- *; auto with arith.
apply H1; apply trans_SUB with (ConsArg q q0); unfold SUB in |- *;
 simpl in |- *; auto with arith.
Save SUB_diff.

Goal
forall (t1 t2 : quasiterm) (f : quasisubst),
SUB t1 t2 -> SUB (Subst f t1) (Subst f t2).
unfold SUB in |- *; simple induction t2; simpl in |- *; intros.
elim H.
elim H.
elim H0; intros h0.
elim h0; auto with arith.
auto with arith.
elim H1; intros h1.
elim h1; auto with arith.
elim h1; intros h2; elim h2; auto with arith.
Save SUB_subst.

Goal
forall (x : var) (t : quasiterm) (f : quasisubst),
IS_IN x t -> V x <> t :>quasiterm -> SUB (f x) (Subst f t).
intros; change (SUB (Subst f (V x)) (Subst f t)) in |- *; apply SUB_subst.
unfold SUB in |- *; cut (V x <> t :>quasiterm); auto with arith;
 cut (IS_IN x t); try apply IS_IN_is_in; auto with arith.
elim t.
(*Case t=(V v)*)
simpl in |- *; intros; absurd (V x = V v :>quasiterm); auto with arith.

(*Case t=(C f)*)
simpl in |- *; intros; absurd False; auto with arith.
(*Case t=(Root f0 q)*)
intros; elim (quasiterm_eq_decP (V x) q); intros.
elim H4; simpl in |- *; auto with arith.
cut (IS_IN x (Root f0 q)); simpl in |- *; auto with arith.
(*Case t=(ConsArg q q0)*)
simpl in |- *; intros.
elim (quasiterm_eq_decP (V x) q); intros; auto with arith.
elim (quasiterm_eq_decP (V x) q0); intros; auto with arith.
elim H3; intros; auto with arith.
Save IS_IN_SUB.

(*****************************************************************)
(******************* Idempotence of a quasisubstitution **************)
(*****************************************************************)

Definition idempotent (s : quasisubst) : Prop :=
  forall x : var, s x = Subst s (s x).

(*****************************************************************)
(************ If for each variable of the range ***********************)
(******************** of a quasisubstitution, ************************)
(************** this is transformed to itself *************************)
(************ the quasisubstitution is idempotent. ********************)
(*****************************************************************)

Goal
forall f : quasisubst,
(forall x : var, range f x -> V x = f x :>quasiterm) -> idempotent f.
unfold idempotent in |- *; intros.
elim (quasiterm_eq_decP (V x) (f x)); intros h.
(*Case <quasiterm>(V x)=(f x)*)
elim h; auto with arith.
(*Case ~<quasiterm>(V x)=(f x)*)
apply trans_equal with (Subst V (f x)).
apply V_stab.
apply eq_restriction_s_t.
intros; apply H; apply range_init with x; auto with arith.
Save range_n_dom_idempotent.

(*****************************************************************)
(***** Conversely if a quasisubstitution is idempotent, then ***********)
(***** the variables of the domain are not in the range. **************)
(*****************************************************************)

Goal
forall f : quasisubst, idempotent f -> forall x : var, dom f x -> ~ range f x.
unfold not in |- *; intros.
elim H0; elim H1; intros.
apply (eq_restriction_t_s (f y) V f); auto with arith.
elim H; elim V_stab with (f y); auto with arith.
Save idempotent_n_range.

(*****************************************************************)
(************* Version without range of the same result. *************)
(*****************************************************************)

Goal
forall f : quasisubst,
idempotent f -> forall x : var, dom f x -> forall y : var, ~ IS_IN x (f y).
intros.
elim (dom_decP f y); intros.
(*Case (dom f y)*)
apply n_range_n_IS_IN; auto with arith.
apply idempotent_n_range; auto with arith.
(*Case ~(dom f y)*)
elim (n_dom f y H1); simpl in |- *.
unfold not in |- *; intros h; absurd (dom f y); auto with arith; elim h;
 auto with arith.
Save idempotent_dom_n_IS_IN.

(*****************************************************************)
(**** If the quasisubstitutions f and g are such that: *******************)
(***** 1)the quasisubstitutions f and g are idempotent, *****************)
(***** 2)the variables images under g are in f(t), ********************)
(***** 3)the variables of the domain of g are in f(t), *****************)
(**** then g o f is idempotent. ************************************)
(*****************************************************************)

Goal
forall (t : quasiterm) (f g : quasisubst),
idempotent f ->
idempotent g ->
under g (Subst f t) ->
over g (Subst f t) -> idempotent (fun x : var => Subst g (f x)).
unfold under in |- *; unfold over in |- *; intros;
 apply range_n_dom_idempotent; intros.
elim H3; intros.
elim (dom_decP g x); intros.
(*Case (dom g x)*)
absurd (IS_IN x (Subst g (f y))); auto with arith.
apply n_IS_IN_Subst.
intros; apply idempotent_dom_n_IS_IN; auto with arith.
(*Case ~(dom g x)*)
elim (dom_decP f x); intros.
(*Case ~(dom g x);(dom f x)*)    
absurd (IS_IN x (f y)).
apply idempotent_dom_n_IS_IN; auto with arith.
apply (n_range_IS_IN_Subst g (f y)); auto with arith.
unfold not in |- *; intros H8; elim H8; intros.
absurd (IS_IN x (Subst f t)).
apply n_IS_IN_Subst.
intros; apply idempotent_dom_n_IS_IN; auto with arith.
apply (H1 x y0); auto with arith.
(*Case ~(dom g x);~(dom f x)*)
elim (n_dom f x H7); simpl in |- *; elim (n_dom g x H6); simpl in |- *;
 auto with arith.
Save idempotent_Fondamental.

(*****************************************************************)
(************** Two evaluations of g(f(t)) : *************************)
(*****************************************************************)

Goal
forall (f g : quasisubst) (t : quasiterm),
Subst g (Subst f t) = Subst (fun x : var => Subst g (f x)) t.
simple induction t; simpl in |- *; intros; auto with arith.
elim H; auto with arith.
elim H; elim H0; auto with arith.
Save comp_subst.

Goal
forall (f g : quasisubst) (t : quasiterm),
Subst (fun x : var => Subst g (f x)) t = Subst g (Subst f t).
intros; symmetry  in |- *; apply comp_subst.
Save exp_comp_subst.

(******************************************************************)
(******** First lemma of induction **********************************)
(****** if the variables of the domain of f and the range of f **********)
(*** are in (ConsArg p1 p2) and if the variables of the domain of g ****)
(****** are in f(ConsArg p3 p4) then the variables of the domain ******)
(***** of g o f are in (ConsArg (ConsArg p1 p3) (ConsArg p2 p4)). ***)
(******************************************************************)

Goal
forall (p1 p2 p3 p4 : quasiterm) (f g : quasisubst),
over f (ConsArg p1 p2) ->
over g (ConsArg (Subst f p3) (Subst f p4)) ->
under f (ConsArg p1 p2) ->
over (fun x : var => Subst g (f x)) (ConsArg (ConsArg p1 p3) (ConsArg p2 p4)).
unfold over, under in |- *; intros.
cut (~ IS_IN x (ConsArg p1 p2)).
intros h; elim (H x h).
simpl in |- *; apply H0; unfold not in |- *; intros; elim H2.

(*n_range_IS_IN_Subst:(f:quasisubst)(t:quasiterm)(x:var)
(~(range f x))->(IS_IN x (Subst f t))->(IS_IN x t)*)

apply n_range_IS_IN_Subst with f.
unfold not in |- *; intros h0; elim h0; intros.
elim h; apply H1 with y; auto with arith.
simpl in |- *; elim H3; auto with arith.
simpl in |- *; unfold not in |- *; intros h; elim H2; simpl in |- *; elim h;
 intros; auto with arith.
Save over_comp.

(******************************************************************)
(******** Second lemma of induction ********************************)
(******* If the variables of the domain of f and the images under f ****)
(******* are in (ConsArg p1 p2) and if ******************************)
(******* the variables of the domain of g and the images under g*******) 
(******* are in f(ConsArg p3 p4) then the images under gof ***********)
(******* are in (ConsArg (ConsArg p1 p3) (ConsArg p2 p4)). **********)
(******************************************************************)

Goal
forall (p1 p2 p3 p4 : quasiterm) (f g : quasisubst),
under f (ConsArg p1 p2) ->
under g (ConsArg (Subst f p3) (Subst f p4)) ->
over f (ConsArg p1 p2) ->
over g (ConsArg (Subst f p3) (Subst f p4)) ->
under (fun x : var => Subst g (f x))
  (ConsArg (ConsArg p1 p3) (ConsArg p2 p4)).
unfold over, dom, under in |- *; intros.

(*under_IS_IN_Subst_IS_IN:(f:quasisubst)(t:quasiterm)
(under f t)->(x:var)(IS_IN x (Subst f t))->(IS_IN x t)*)

apply under_IS_IN_Subst_IS_IN with g.
(*Goal (under...)*) 
unfold under, over, dom in |- *; intros.
cut (IS_IN x0 (Subst f (ConsArg p3 p4))).
intros H7; elim (IS_IN_Subst_exi_IS_IN f (ConsArg p3 p4) x0 H7); intros.
elim H8; intros h1 h2.
apply under_IS_IN_Subst_IS_IN with f.
unfold under in |- *; intros.
elim H with x2 y1; simpl in |- *; auto with arith.
elim (H0 x0 y0); simpl in |- *; auto with arith.
elim (H0 x0 y0); simpl in |- *; auto with arith.
(*Goal (IS_IN x...)*) 
elim (IS_IN_Subst_exi_IS_IN g (f y) x H4); intros.
elim H5; intros.
apply IS_IN_Subst_IS_IN with x0; auto with arith.
elim (dom_decP f y); intros.
(**)
elim (H x0 y); simpl in |- *; auto with arith.
cut (IS_IN x0 (f y)); auto with arith; elim (n_dom f y H8); intros.
elim (dom_decP g x0); intros.
(**)
elim (IS_IN_decP x0 (ConsArg (Subst f p3) (Subst f p4))); intros h.
elim (IS_IN_Subst_exi_IS_IN f (ConsArg p3 p4) x0 h); intros x1 h1; elim h1;
 intros.
elim (dom_decP f x1); intros.
(**)
elim H with x0 x1; simpl in |- *; auto with arith.
(**)
cut (IS_IN x0 (f x1)); auto with arith; elim (n_dom f x1 H13); intros.
cut (IS_IN x1 (ConsArg p3 p4)); auto with arith; elim H14.
simpl in |- *; intros h2; elim h2; intros; auto with arith.
absurd (V x0 = g x0 :>quasiterm); auto with arith.
absurd (V y = Subst g (f y) :>quasiterm); auto with arith.
elim (n_dom f y H8); simpl in |- *; elim H9; elim (n_dom g x0 H10);
 auto with arith.
Save under_comp.

(*****************************************************************)
(*** If the domain of the quasisubstitution f is finite, *****************)
(*** then either f is the injection V from var is_ino quasiterm, ********)
(******** or there exists x in var such that f(x) is not V(x). **********)
(*** In the second case f decreases the number of variables. ***********)
(*****************************************************************)

Goal
forall (t : quasiterm) (f : quasisubst),
over f t -> (exists x : var, V x <> f x) \/ (forall v : var, V v = f v).
(*cut*)
cut
 (forall (l : listv) (f : quasisubst),
  (forall x : var, V x <> f x :>quasiterm -> IS_IN_LV x l) ->
  (exists x : var, V x <> f x :>quasiterm) \/
  (forall v : var, V v = f v :>quasiterm)).
unfold over in |- *; intros.
apply H with (list_var t); intros.
apply IS_IN_IS_IN_LV.
elim (IS_IN_decP x t); intros; auto with arith.
absurd (V x = f x :>quasiterm); auto with arith.
(*proof of the cut*)
simple induction l; simpl in |- *; intros.
right; intros.
elim (quasiterm_eq_decP (V v) (f v)); intros; auto with arith.
elim (H v H0).
elim (quasiterm_eq_decP (V v) (f v)); intros.
apply (H f); intros.
elim (H0 x H2); intros; auto with arith.
absurd (V v = f v :>quasiterm); auto with arith; elim H3; auto with arith.
left; exists v; auto with arith.
Save ident_or_not.

Goal
forall (t : quasiterm) (f : quasisubst),
over f t ->
{x : var | V x <> f x :>quasiterm} +
{(forall x : var, V x = f x :>quasiterm)}.
cut
 (forall (l : listv) (f : quasisubst),
  (forall x : var, V x <> f x :>quasiterm -> IS_IN_LV x l) ->
  {x : var | V x <> f x :>quasiterm} +
  {(forall x : var, V x = f x :>quasiterm)}).
unfold over in |- *; intros.
apply H with (list_var t); intros.
apply IS_IN_IS_IN_LV.
elim (IS_IN_decP x t); intros; auto with arith.
absurd (V x = f x :>quasiterm); auto with arith.
(**)
simple induction l; simpl in |- *; intros.
right; intros.
elim (quasiterm_eq_decP (V x) (f x)); intros; auto with arith.
elim (H x H0).
elim (quasiterm_eq_decS (V v) (f v)); intros.
apply (H f); intros.
elim (H0 x H1); intros; auto with arith.
absurd (V v = f v :>quasiterm); auto with arith; elim H2; auto with arith.
left; exists v; auto with arith.
Save ident_or_notS.

(*****************************************************************)
(******* If f is idempotent and if the variables of the domain of f ****)
(******* and the images under f are in (ConsArg t1 t3) *************) 
(******* and if the domain of f is not empty ***********************) 
(***** then the number of different variables in ConsArg(f(t2),f(t4)) ***)
(***** is strictly less than in ConsArg(ConsArg(t1,t2),ConsArg(t3,t4)).**)
(*****************************************************************)

Goal
forall (t1 t2 t3 t4 : quasiterm) (n : nat),
DIFFELNB (list_var (ConsArg (ConsArg t1 t2) (ConsArg t3 t4))) n ->
forall f : quasisubst,
idempotent f ->
over f (ConsArg t1 t3) ->
under f (ConsArg t1 t3) ->
(exists x : var, V x <> f x :>quasiterm) ->
forall n0 : nat,
DIFFELNB (list_var (ConsArg (Subst f t2) (Subst f t4))) n0 -> S n0 <= n.
unfold over, under in |- *; intros.
elim H3; intros.
apply
 DIFFELNB_st_inclv_le_S
  with
    (list_var (ConsArg (Subst f t2) (Subst f t4)))
    (list_var (ConsArg (ConsArg t1 t2) (ConsArg t3 t4))); 
 auto with arith.
apply st_inclv_init with x.
change (~ IS_IN_LV x (list_var (Subst f (ConsArg t2 t4)))) in |- *.
unfold not in |- *; intros; cut (IS_IN x (Subst f (ConsArg t2 t4))); intros.
2: apply IS_IN_LV_IS_IN; auto with arith.
elim (IS_IN_Subst_exi_IS_IN f (ConsArg t2 t4) x H7); intros.
elim H8; intros.
absurd (IS_IN x (f x0)); auto with arith; apply idempotent_dom_n_IS_IN;
 auto with arith.
apply IS_IN_IS_IN_LV; elim (IS_IN_decP x (ConsArg t1 t3)); intros.
cut (IS_IN x (ConsArg t1 t3)).
2: auto with arith.
simpl in |- *; intros h; elim h; auto with arith.
absurd (V x = f x :>quasiterm); auto with arith.
intros; cut (IS_IN y (Subst f (ConsArg t2 t4))).
2: apply IS_IN_LV_IS_IN; auto with arith.
intros; apply IS_IN_IS_IN_LV;
 elim (IS_IN_Subst_exi_IS_IN f (ConsArg t2 t4) y H7); 
 intros.
elim H8; intros.
elim (dom_decP f x0); intros.
cut (IS_IN y (ConsArg t1 t3)).
2: apply (H2 y x0); auto with arith.
simpl in |- *; intros h; elim h; auto with arith.
cut (V x0 = f x0 :>quasiterm).
2: apply n_dom; auto with arith.
intros; cut (y = x0 :>var).
intros h; cut (IS_IN x0 (ConsArg t2 t4)).
2: auto with arith.
elim h; simpl in |- *; intros h1; elim h1; auto with arith.
cut (IS_IN y (f x0)); auto with arith; elim H12; simpl in |- *; auto with arith.
Save f_n_id_minus.

(**********************************************************************)
(*************** The iterative construction of the unifiers, ****************)
(****** Here is a method which does not requires the axiom of choice *******)
(***************** but uses an induction over the integers. ****************)
(**********************************************************************)

Inductive elem_subst (x : var) (t : quasiterm) (f : quasisubst) : Prop :=
    elem_subst_init :
      (forall y : var, x <> y -> V y = f y) ->
      (forall y : var, x = y -> t = f y) -> elem_subst x t f. 

Goal
forall (t : quasiterm) (n : var) (f : quasisubst),
{g : quasisubst | t = g n /\ (forall p : nat, n <> p -> f p = g p)}.
simple induction n.
intros. exists
  (fun m : nat => match m return quasiterm with
                  | O => t
                  | S p => f m
                  end); split; auto with arith.
simple induction p; auto with arith.
intros; elimtype False; auto with arith.
intros.
elim (H (fun x : nat => f (S x))); intros g0 h0; elim h0; intros.
exists
 (fun m : nat => match m return quasiterm with
                 | O => f 0
                 | S p => g0 p
                 end); split; auto with arith.
simple induction p; auto with arith.
Save sig_elem_subst0.

Goal forall (x : var) (t : quasiterm), {f : quasisubst | elem_subst x t f}.
intros; elim (sig_elem_subst0 t x V); intros.
exists x0; elim p; intros; apply elem_subst_init; auto with arith.
intros y0 h; elim h; auto with arith.
Save sig_elem_subst.

Goal
forall (t : quasiterm) (x : var) (f : quasisubst),
(forall y : var, x <> y -> V y = f y) -> ~ IS_IN x t -> t = Subst f t.
intros.
replace (Subst f t) with (Subst V t); try apply V_stab.
apply eq_restriction_s_t.
intros; elim (var_eq_decP x x0); intros; auto with arith.
absurd (IS_IN x0 t); auto with arith; elim H2; auto with arith.
Save elem_subst_conserve.

(*****************************************************************)
(************** Order in quasisubst ********************************)
(*****************************************************************)

Inductive less_subst (f g : quasisubst) : Prop :=
    less_subst_init :
      forall h : quasisubst,
      (forall x : var, Subst h (f x) = g x) -> less_subst f g.

(*****************************************************************)
(********************** Definition of an unifier: ********************)
(*****************************************************************)

Definition unif (f : quasisubst) (t u : quasiterm) : Prop :=
  Subst f t = Subst f u.

(*****************************************************************)
(***************** Definition of a minimal unifier: ******************)
(*****************************************************************)

Definition min_unif (f : quasisubst) (t u : quasiterm) : Prop :=
  forall g : quasisubst, unif g t u -> less_subst f g.

(*****************************************************************)
(***************** Specification of the problem of the unification ******)
(*****************************************************************)
(********************* Unif defines the minimal unifiers.*************)
(*****************************************************************)
