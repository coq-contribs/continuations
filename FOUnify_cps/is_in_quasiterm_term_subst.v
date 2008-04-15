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
(*                       is_in_quasiterm_term_subst.v                       *)
(****************************************************************************)

Require Import Arith.
Require Import nat_complements.
Require Import nat_term_eq_quasiterm.

(***********************************************************************)
(******************* VARIABLE IN A QUASITERM *********************)
(***********************************************************************)

Inductive is_in (x : var) : quasiterm -> Prop :=
  | is_in_init : is_in x (V x)
  | is_in_Root :
      forall (l : fun_) (t : quasiterm), is_in x t -> is_in x (Root l t)
  | is_in_ConsArg1 :
      forall t1 t2 : quasiterm, is_in x t1 -> is_in x (ConsArg t1 t2)
  | is_in_ConsArg2 :
      forall t1 t2 : quasiterm, is_in x t2 -> is_in x (ConsArg t1 t2).

Fixpoint IS_IN (x : var) (t : quasiterm) {struct t} : Prop :=
  match t return Prop with
  | V y => x = y
  | C l => False
  | Root l t => IS_IN x t
  | ConsArg t1 t2 => IS_IN x t1 \/ IS_IN x t2
  end.


Lemma IS_IN_is_in : forall (x : var) (t : quasiterm), IS_IN x t -> is_in x t.
simple induction t.
intros.
elim H; apply is_in_init.
intros; elim H.
intros; apply is_in_Root; auto.
intros; elim H1; intros.
apply is_in_ConsArg1; auto.
apply is_in_ConsArg2; auto.
Qed.


Lemma is_in_IS_IN : forall (x : var) (t : quasiterm), is_in x t -> IS_IN x t.
intros; elim H; simpl in |- *; auto.
Qed.

(***********************************************************************)
(************************* IS_IN decidability *****************************)
(***********************************************************************)

Lemma IS_IN_decS :
 forall (x : var) (t : quasiterm), {IS_IN x t} + {~ IS_IN x t}.
simple induction t.
intro; elim (var_eq_decS x v); intros; simpl in |- *; auto.
intros; right; auto.
intros f y h; elim h; intros; simpl in |- *; auto.
intros y h y0 h0; elim h; elim h0; intros; simpl in |- *; auto.
right; tauto.
Qed.

Lemma IS_IN_decP : forall (x : var) (t : quasiterm), IS_IN x t \/ ~ IS_IN x t.
intros; elim (IS_IN_decS x t); intros; auto.
Qed.

(**********************************************************************)
(************************** End of IS_IN *******************************)
(**********************************************************************)

(***********************************************************************)
(********************** QUASISUBSTITUTIONS *************************)
(***********************************************************************)

Definition quasisubst := var -> quasiterm.

Fixpoint Subst (f : quasisubst) (t : quasiterm) {struct t} : quasiterm :=
  match t return quasiterm with
  | V x => f x
  | C x => C x
  | Root l t => Root l (Subst f t)
  | ConsArg t1 t2 => ConsArg (Subst f t1) (Subst f t2)
  end.

(*---------------------------------------------*)
(*------------ Verifications on the terms:begin -------------*)
(*---------------------------------------------*)

Inductive term_subst (l : list_nat) (f : quasisubst) : Prop :=
    term_subst_init : (forall x : var, term l (f x)) -> term_subst l f.

(***********************************************************************)
(********************** If (term_subst l f), *******************************)
(********* then Length, SIMPLE, (L_TERM l) and (term l) ****************) 
(******************* are stable by (Subst f). ******************************)
(***********************************************************************)

Lemma term_subst_eq_Length :
 forall (l : list_nat) (f : quasisubst) (t : quasiterm),
 term_subst l f -> Length t = Length (Subst f t) :>nat.
simple induction t; intros; elim H; simpl in |- *; auto.
intros h; elim (h v).
elim (f v); simpl in |- *; auto.
intros.
absurd False; auto.
Qed.

Lemma SIMPLE_term_subst :
 forall (l : list_nat) (f : quasisubst),
 term_subst l f -> forall t : quasiterm, SIMPLE t -> SIMPLE (Subst f t).
simple induction t; simpl in |- *; auto.
intros; elim H; intros h; elim (h v); intros; auto.
Qed.

Lemma L_TERM_term_subst :
 forall (l : list_nat) (t : quasiterm),
 L_TERM l t -> forall f : quasisubst, term_subst l f -> L_TERM l (Subst f t).
intros l t H; cut (l_term l t).
2: try apply L_TERM_l_term; auto.
intros h; elim h; simpl in |- *; auto.
intros x f h0; elim h0.
intros h1; elim (h1 x); auto.
intros.
split; auto.
replace (arity l f) with (Length t0).
apply term_subst_eq_Length with l; auto.
intros.
split; auto.
apply SIMPLE_term_subst with l; auto.
Qed.

Lemma term_term_subst :
 forall (l : list_nat) (t : quasiterm),
 term l t -> forall f : quasisubst, term_subst l f -> term l (Subst f t).
intros; apply term_init.
elim H; intros; apply L_TERM_term_subst; auto.
elim H; intros; apply SIMPLE_term_subst with l; auto.
Qed.

(*---------------------------------------------*)
(*------------ Verifications on the terms:end --------------*)
(*---------------------------------------------*)

(***********************************************************************)
(************** Properties linked to IS_IN and Subst ***********************)
(***********************************************************************)

Lemma n_IS_IN_Subst :
 forall (f : quasisubst) (t : quasiterm) (x : var),
 (forall y : var, ~ IS_IN x (f y)) -> ~ IS_IN x (Subst f t).
simple induction t; simpl in |- *; auto.
intros; unfold not in |- *; intros h; elim h; intros.
elim (H x); auto.
elim (H0 x); auto.
Qed.

Lemma IS_IN_Subst_IS_IN :
 forall (f : quasisubst) (t : quasiterm) (x x0 : var),
 IS_IN x (f x0) -> IS_IN x0 t -> IS_IN x (Subst f t).
simple induction t; simpl in |- *; auto.
intros.
elim H0; auto.
intros.
elim H2; intros.
left; apply (H x x0); auto.
right; apply (H0 x x0); auto.
Qed.

(***********************************************************************)
(**** If two quasisubstitutions have the same restriction ********************)
(************** on the set of the variables of t, **************************)
(************** then they transform t in the same quasiterm. **************)
(***********************************************************************)

Lemma eq_restriction_s_t :
 forall (t : quasiterm) (f g : quasisubst),
 (forall x : var, IS_IN x t -> f x = g x :>quasiterm) ->
 Subst f t = Subst g t :>quasiterm.
simple induction t; simpl in |- *; auto.
intros.
elim (H f0 g); auto.
intros.
elim (H f g); elim (H0 f g); auto.
Qed.

(***********************************************************************)
(******* If two quasisubstitutions transform t in the same quasiterm, ********)
(***** then they have the same restriction on the set of the variables of t.****)
(***********************************************************************)

Lemma eq_restriction_t_s :
 forall (t : quasiterm) (f g : quasisubst),
 Subst f t = Subst g t -> forall x : var, IS_IN x t -> f x = g x :>quasiterm.
simple induction t; simpl in |- *; intros.
rewrite H0; auto.
contradiction.                         
apply H; [ injection H0; auto | auto ].
elim H2; intros.
apply H; [ injection H1; auto | auto ].
apply H0; [ injection H1; auto | auto ].
Qed.

(***********************************************************************)
(********************* End of quasisubstitutions **************************)
(***********************************************************************)
