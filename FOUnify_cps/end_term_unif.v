(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(* Jean-Francois.Monin@lannion.cnet.fr                                      *)
(* February 1995, Coq V5.10                                                 *)
(*                                                                          *)
(****************************************************************************)
(*                              end_term_unif.v                             *)
(****************************************************************************)

Require Import Arith.
Require Import nat_complements.
Require Import nat_term_eq_quasiterm.
Require Import is_in_quasiterm_term_subst.
Require Import listv_is_in_lv.
Require Import deb_term_unif.

(*****************************************************************)
(***************** Specification of the problem of the unification ******)
(*****************************************************************)
(********************* Unif defines the minimal unifiers.*************)
(*****************************************************************)

(* Only the success part *)
Inductive Unification_s (t1 t2 : quasiterm) : Set :=
    Unif_succeed_def :
      forall f : quasisubst,
      unif f t1 t2 ->
      idempotent f ->
      over f (ConsArg t1 t2) ->
      under f (ConsArg t1 t2) ->
      min_unif f t1 t2
      (*------------ Verifications on the terms:begin -------------*)
      (**)  ->
      (forall l : list_nat,
       L_TERM l t1 ->
       L_TERM l t2
       (**)  -> Length t1 = Length t2 -> term_subst l f)
      (*------------ Verifications on the terms:end --------------*)
       -> Unification_s t1 t2.

(* Failure part : only a Prop *)
Inductive Unification_f (t1 t2 : quasiterm) : Prop :=
    Unif_fail_def :
      (forall f : quasisubst, Subst f t1 <> Subst f t2) ->
      Unification_f t1 t2.

(* The following is equivalent to the original "Unification"  *)
(* an will be used only once (in unif_call) at the end of the *)
(* development.                                               *)
Inductive Unification_or_fail (t1 t2 : quasiterm) : Set :=
  | Unification_or_fail_succeed :
      Unification_s t1 t2 -> Unification_or_fail t1 t2
  | Unification_or_fail_fail :
      Unification_f t1 t2 -> Unification_or_fail t1 t2.

(*****************************************************************)
(************** Failure in the unification with the head symbol: *******)
(*****************************************************************)

Inductive head_diff : quasiterm -> quasiterm -> Prop :=
  | Fail_hd1 :
      forall (l : fun_) (t1 t2 : quasiterm), head_diff (C l) (ConsArg t1 t2)
  | Fail_hd2 :
      forall (l : fun_) (t1 t2 : quasiterm), head_diff (ConsArg t1 t2) (C l)
  | Fail_hd3 :
      forall (l l0 : fun_) (t : quasiterm), head_diff (C l) (Root l0 t)
  | Fail_hd4 :
      forall (l l0 : fun_) (t : quasiterm), head_diff (Root l0 t) (C l)
  | Fail_hd5 :
      forall (t1 t2 t3 : quasiterm) (l : fun_),
      head_diff (ConsArg t1 t2) (Root l t3)
  | Fail_hd6 :
      forall (t1 t2 t3 : quasiterm) (l : fun_),
      head_diff (Root l t3) (ConsArg t1 t2).

Require Import cps_Nx.

Section algorithmes.

Load "DeclareNx".

(* New version of Unification with exceptions *)
Definition Unification (t1 t2 : quasiterm) :=
  Unification_f t1 t2 \/+ Unification_s t1 t2. 

(* An instance of identity, useful only for its type, cf. unif_call *)
Definition Unification_build (t1 t2 : quasiterm) :
  Unification t1 t2 ->
  (Unification_f t1 t2 -> P) -> (Unification_s t1 t2 -> X) -> X :=
  Nx_handle (Unification_f t1 t2) (Unification_s t1 t2).
   

Definition Nxunif_unit (t1 t2 : quasiterm) :
  Unification_s t1 t2 -> Unification t1 t2 :=
  Nx_unit (Unification_f t1 t2) (Unification_s t1 t2).

Definition Nxunif_raise (t1 t2 : quasiterm) :
  Unification_f t1 t2 -> Unification t1 t2 :=
  Nx_raise (Unification_f t1 t2) (Unification_s t1 t2).

(* New version of Unif_succeed *)
Definition Unif_succeed (t1 t2 : quasiterm) (f : quasisubst)
  (u : unif f t1 t2) (i : idempotent f) (o : over f (ConsArg t1 t2))
  (u0 : under f (ConsArg t1 t2)) (m : min_unif f t1 t2)
  (t : forall l : list_nat,
       L_TERM l t1 -> L_TERM l t2 -> Length t1 = Length t2 -> term_subst l f) :=
  Nxunif_unit t1 t2 (Unif_succeed_def t1 t2 f u i o u0 m t).

(* New version of Unif_fail, to be used when raising an exception. *)
(* Warning: Unif_fail_def has to be used for transmitting an       *)
(* information "an exception must have been raised".               *)
Definition Unif_fail (t1 t2 : quasiterm)
  (e : forall f : quasisubst, Subst f t1 <> Subst f t2) :=
  Nxunif_raise t1 t2 (Unif_fail_def t1 t2 e).


Definition Unification_elim (t1 t2 t1' t2' : quasiterm) :
  (Unification_s t1 t2 -> Unification t1' t2') ->
  (Unification_f t1 t2 -> Unification_f t1' t2') ->
  Unification t1 t2 -> Unification t1' t2' :=
  Nx_elim_Nx (Unification_s t1 t2) (Unification_s t1' t2')
    (Unification_f t1 t2) (Unification_f t1' t2').

(* Plays the role of Unification_rec;                *)
(* "Elim H" becomes "Elimunif H",                    *)
(* at least when H is not a product                  *)
(* In the development H is a product in only one     *)
(* instance, namely (H0 q1) in proof_unif;           *)
(* we can use a "Cut" in such situations.            *)
Goal
forall t1 t2 t1' t2' : quasiterm,
(forall (f : quasisubst) (u : unif f t1 t2) (i : idempotent f)
   (o : over f (ConsArg t1 t2)) (u0 : under f (ConsArg t1 t2))
   (m : min_unif f t1 t2)
   (t : forall l : list_nat,
        L_TERM l t1 -> L_TERM l t2 -> Length t1 = Length t2 -> term_subst l f),
 Unification t1' t2') ->
(forall n : forall f : quasisubst, Subst f t1 <> Subst f t2,
 Unification_f t1' t2') -> Unification t1 t2 -> Unification t1' t2'.
  intros t1 t2 t1' t2' inh_s inh_f nu.
  apply Unification_elim with (3 := nu).
    intro u; elim u; exact inh_s.
    intro u; elim u; exact inh_f.
Defined Unif_elim.

Ltac Elimunif c := apply Unif_elim with (3 := c).

Goal forall t1 t2 : quasiterm, head_diff t1 t2 -> Unification t1 t2.
intros; apply Unif_fail; elim H; intros.
apply Diff with BC; simpl in |- *; auto with arith.
apply Diff with BConsArg; simpl in |- *; auto with arith.
apply Diff with BC; simpl in |- *; auto with arith.
apply Diff with BRoot; simpl in |- *; auto with arith.
apply Diff with BConsArg; simpl in |- *; auto with arith.
apply Diff with BRoot; simpl in |- *; auto with arith.
Save Decomp_fail.

Hint Resolve Fail_hd1 Fail_hd2 Fail_hd3 Fail_hd4 Fail_hd5 Fail_hd6
  Decomp_fail.

(*****************************************************************)
(*************** Symetry of the problem of the unification : **********)
(*****************************************************************)

Goal forall t1 t2 : quasiterm, Unification t1 t2 -> Unification t2 t1.
intros; Elimunif ipattern:(H);
 unfold idempotent, over, under, min_unif, unif in |- *; 
 intros.
apply Unif_succeed with f;
 unfold idempotent, over, under, min_unif, unif in |- *; 
 auto with arith; intros.
apply o; unfold not in |- *; intros h; elim H0; simpl in |- *; elim h;
 auto with arith.
simpl in |- *; elim (u0 x y); auto with arith.
apply Unif_fail_def; intros.
unfold not in |- *; intros; elim (n f); auto with arith.
Save sym_Unification.

(*****************************************************************)
(*********** Unification when one of the terms is a variable : ********)
(*****************************************************************)

Goal forall (n : var) (t : quasiterm), Unification (V n) t.
intros; elim (IS_IN_decS n t); intros.
elim (quasiterm_eq_decS (V n) t); intros.
(*Case (IS_IN n t) and <quasiterm>(V n)=t*)
elim a0; apply Unif_succeed with (fun x : var => V x);
 unfold unif, idempotent, over, under in |- *; simpl in |- *; 
 auto with arith; intros.
absurd (V y = V y); auto with arith.
unfold min_unif, unif in |- *; intros.
apply less_subst_init with g; auto with arith.
(*------------ Verifications on the terms:begin -------------*)
apply term_subst_init; intros; apply term_init; simpl in |- *; auto with arith.
(*------------ Verifications on the terms:end --------------*)
(*Case (IS_IN n t) and ~<quasiterm>(V n)=t*)
apply Unif_fail; intros; apply SUB_diff.
simpl in |- *; apply IS_IN_SUB; auto with arith.
(*Case ~(IS_IN n t)*)
elim (sig_elem_subst n t); intros.
apply Unif_succeed with x; unfold unif, idempotent, over, under in |- *;
 simpl in |- *; elim p; intros.
replace (x n) with t; auto with arith.
apply elem_subst_conserve with n; auto with arith.
elim (var_eq_decP n x0); intros.
elim (H0 x0); auto with arith.
apply elem_subst_conserve with n; auto with arith.
elim (H x0); simpl in |- *; auto with arith.
elim (var_eq_decP x0 n); intros.
elim H1; auto with arith.
elim (H x0); auto with arith.
(*BOGUS: Unfold not;Intros;Elim H2;Auto with arith.*)
elim (var_eq_decP n y); intros.
replace t with (x y); auto with arith.
symmetry  in |- *; auto with arith.
absurd (V y = x y); auto with arith.
unfold min_unif, unif in |- *; intros.
apply less_subst_init with g.
intros; elim (var_eq_decP n x0); intros.
elim H2; elim (H0 n); auto with arith.
elim (H x0); auto with arith.
(*------------ Verifications on the terms:begin -------------*)
apply term_subst_init.
intros; elim (var_eq_decP x0 n); intros.
elim (H0 x0); auto with arith.
apply Length_SO_term; auto with arith.
elim (H x0).
apply term_init; simpl in |- *; auto with arith.
unfold not in |- *; intros; elim H4; auto with arith.
(*------------ Verifications on the terms:end --------------*)
Save UnifV1.

Goal forall (t : quasiterm) (x : var), Unification t (V x).
intros; apply sym_Unification; apply UnifV1.
Save UnifV2.

Hint Resolve UnifV1 UnifV2.

(*****************************************************************)
(********** Unification when one of the terms is a constant : ********)
(*****************************************************************)

Goal forall (t : quasiterm) (l : fun_), Unification (C l) t.
simple induction t; auto with arith.
intros; elim (fun_eq_decS l f); intros.
elim a; apply Unif_succeed with V;
 unfold unif, idempotent, over, under in |- *; simpl in |- *; 
 auto with arith.
(*Intros;Absurd <quasiterm>(V y)=(V y);Auto with arith.*)
unfold min_unif, unif in |- *; intros.
apply less_subst_init with g; auto with arith.
(*------------ Verifications on the terms:begin -------------*)
intros; apply term_subst_init; intros; apply term_init; simpl in |- *;
 auto with arith.
(*------------ Verifications on the terms:end --------------*)
apply Unif_fail; intros; simpl in |- *.
apply C_diff_C; auto with arith.
Save UnifC1.

Goal forall (t : quasiterm) (l : fun_), Unification t (C l).
intros; apply sym_Unification; apply UnifC1.
Save UnifC2.

Hint Resolve UnifC1 UnifC2.

(*****************************************************************)
(********** Link between the unification of  t1 and t2 ****************)
(****** and the unification of (Root l1 t1) and (Root l2 t2) : *********)
(*****************************************************************)

Goal
forall (t1 t2 : quasiterm) (l1 l2 : fun_),
Unification t1 t2 -> Unification (Root l1 t1) (Root l2 t2).
intros; elim (fun_eq_decS l1 l2); intros.
elim a; Elimunif H; unfold unif, idempotent, over, under in |- *; intros.
apply Unif_succeed with f; unfold unif, idempotent, over, under in |- *;
 simpl in |- *; auto with arith.
elim u; auto with arith.
unfold min_unif, unif in |- *; simpl in |- *; intros.
apply m; unfold unif in |- *.
apply proj_Root2 with l1 l1; auto with arith.
intros.
elim H0; elim H1; intros; apply t; auto with arith.
elim H4; auto with arith.
apply Unif_fail_def; intros.
simpl in |- *; apply Root_diff_Root; auto with arith.
apply Unif_fail; intros.
simpl in |- *; apply Root_diff_Root; auto with arith.
Save UnifRoot.

Hint Resolve UnifRoot.

(********************************************************************)
(********** The failure of the unification of t1 and t3 implies ************)
(* the failure of the unification of (ConsArg t1 t2) and (ConsArg t3 t4) : **)
(********************************************************************)

Goal
forall t1 t2 t3 t4 : quasiterm,
(forall f : quasisubst, Subst f t1 <> Subst f t3 :>quasiterm) ->
Unification_f (ConsArg t1 t2) (ConsArg t3 t4).
intros; apply Unif_fail_def; intros.
simpl in |- *; apply ConsArg_diff_ConsArg; auto with arith.
Save UnifConsArgfail1.

Hint Resolve UnifConsArgfail1.

(*****************************************************************)
(********** The unification of the ground terms : ********************)
(*****************************************************************)

Goal
forall t1 t2 : quasiterm,
DIFFELNB (list_var (ConsArg t1 t2)) 0 -> Unification t1 t2.
intros; elim (quasiterm_eq_decS t1 t2); intros.
elim a.
apply Unif_succeed with V;
 unfold unif, idempotent, over, under, min_unif in |- *; 
 auto with arith.
intros.
absurd (V y = V y); auto with arith.
intros; apply less_subst_init with g; auto with arith.
intros; apply term_subst_init; intros; apply term_init; simpl in |- *;
 auto with arith.
apply Unif_fail; intros.
elim (clossubst t1 f).
elim (clossubst t2 f); auto with arith.
apply closConsArg2 with t1; apply DIFFELNB_O_clos; auto with arith.
apply closConsArg1 with t2; apply DIFFELNB_O_clos; auto with arith.
Save Unif_DIFFELNB_O.

(*****************************************************************)
(********* The number of variables of (ConsArg t1 t3)  **************)
(************ and the one of the variables of (ConsArg t2 t4) ********)
(********* are less or equal to the number of the variables of *********)
(********** (ConsArg (ConsArg t1 t2)(ConsArg t3 t4)). **************) 
(*****************************************************************)

Goal
forall (t1 t2 t3 t4 : quasiterm) (n : nat),
DIFFELNB (list_var (ConsArg (ConsArg t1 t2) (ConsArg t3 t4))) n ->
forall n0 : nat,
DIFFELNB (list_var (ConsArg t2 t4)) n0 -> {S n0 <= n} + {n0 = n :>nat}.
intros; elim (le_decS n0 n); intros.
apply (le_S_eqS n0 n a).
absurd (n0 <= n); auto with arith.
apply
 inclv_le
  with
    (list_var (ConsArg t2 t4))
    (list_var (ConsArg (ConsArg t1 t2) (ConsArg t3 t4))); 
 auto with arith.
apply inclv_init; intros; apply IS_IN_IS_IN_LV; simpl in |- *.
elim (IS_IN_LV_IS_IN (ConsArg t2 t4) y H1); auto with arith.
Save DIFFELNB_ConsArg_ConsArg24_le.
 
Goal
forall (t1 t2 t3 t4 : quasiterm) (n : nat),
DIFFELNB (list_var (ConsArg (ConsArg t1 t2) (ConsArg t3 t4))) n ->
forall n0 : nat,
DIFFELNB (list_var (ConsArg t1 t3)) n0 -> {S n0 <= n} + {n0 = n :>nat}.
intros; elim (le_decS n0 n); intros h.
apply (le_S_eqS n0 n h).
absurd (n0 <= n); auto with arith.
apply
 inclv_le
  with
    (list_var (ConsArg t1 t3))
    (list_var (ConsArg (ConsArg t1 t2) (ConsArg t3 t4))); 
 auto with arith.
apply inclv_init; intros; apply IS_IN_IS_IN_LV; simpl in |- *.
elim (IS_IN_LV_IS_IN (ConsArg t1 t3) y H1); auto with arith.
Save DIFFELNB_ConsArg_ConsArg13_le.

Hint Resolve eq_V_stab.

(*****************************************************************)
(******************** If f unifies t1 and u1 ************************)
(********** and if g unifies (Subst f t2) (Subst f u2), ****************)
(************** then [x:var](Subst g (f x)) unifies ********************)
(************** (ConsArg t1 t2) et (ConsArg u1 u2). ****************)
(*****************************************************************)

Goal
forall (t1 t2 u1 u2 : quasiterm) (f g : quasisubst),
unif f t1 u1 ->
unif g (Subst f t2) (Subst f u2) ->
unif (fun x : var => Subst g (f x)) (ConsArg t1 t2) (ConsArg u1 u2).
unfold unif in |- *; simpl in |- *; intros.
elim (comp_subst f g t2); elim (comp_subst f g u2); elim (comp_subst f g t1);
 elim (comp_subst f g u1).
elim H; elim H0; auto with arith.
Save unif_comp.

Hint Resolve unif_comp.

(*****************************************************************)
(**************** If f is a minimal unifier of t1 and u1 *************)
(********** and if g is a one of (Subst f t2) (Subst f u2), then *******)
(********************** [x:var](Subst g (f x)) ***********************) 
(************ is a one of (ConsArg t1 t2) and (ConsArg u1 u2) : ****)
(*****************************************************************)

Goal
forall (t1 t2 u1 u2 : quasiterm) (f g : quasisubst),
min_unif f t1 u1 ->
min_unif g (Subst f t2) (Subst f u2) ->
min_unif (fun x : var => Subst g (f x)) (ConsArg t1 t2) (ConsArg u1 u2).
unfold min_unif, unif in |- *; simpl in |- *; intros.
elim (H g0); intros.
elim (H0 h); intros.
apply less_subst_init with h0.
intros; elim (H2 x).
elim (exp_comp_subst g h0 (f x)).
apply eq_restriction_s_t; auto with arith.
elim (exp_comp_subst f h t2); elim (exp_comp_subst f h u2).
transitivity (Subst g0 t2).
apply eq_restriction_s_t; auto with arith.
transitivity (Subst g0 u2).
apply proj_ConsArg2 with (Subst g0 t1) (Subst g0 u1); auto with arith; intros.
apply eq_restriction_s_t; auto with arith.
apply proj_ConsArg1 with (Subst g0 t2) (Subst g0 u2); auto with arith; intros.
Save min_unif_comp.

Hint Resolve min_unif_comp.

(*------------ Verifications on the terms:begin -------------*)


Goal
forall (t1 t2 t3 t4 : quasiterm) (f g : quasisubst) (l : list_nat),
L_TERM l (ConsArg t1 t2) ->
L_TERM l (ConsArg t3 t4) ->
Length (ConsArg t1 t2) = Length (ConsArg t3 t4) :>nat ->
(forall l : list_nat,
 L_TERM l t1 -> L_TERM l t3 -> Length t1 = Length t3 :>nat -> term_subst l f) ->
(forall l : list_nat,
 L_TERM l (Subst f t2) ->
 L_TERM l (Subst f t4) ->
 Length (Subst f t2) = Length (Subst f t4) :>nat -> term_subst l g) ->
term_subst l (fun x : var => Subst g (f x)).
simpl in |- *; intros.
elim H; elim H0; intros.
elim H5; elim H7; intros.
cut (term_subst l f).
intros hyp; apply term_subst_init.
intros; simpl in |- *; apply term_term_subst.
elim hyp; auto with arith.
apply H3; try apply L_TERM_term_subst; auto with arith.
elim (term_subst_eq_Length l f t2); elim (term_subst_eq_Length l f t4);
 auto with arith.
cut (Length t1 + Length t2 = Length t3 + Length t4); auto with arith.
replace (Length t1) with 1; try apply SIMPLE_SO; auto with arith.
replace (Length t3) with 1; try apply SIMPLE_SO; auto with arith.
apply (H2 l H8 H10).
replace (Length t1) with 1; try apply SIMPLE_SO; auto with arith.
Save term_subst_comp.
(*------------ Verifications on the terms:end --------------*)

(*****************************************************************)
(********** If f is a minimal unifier of t1 and t3 *******************)
(********** whose domain and image are in (ConsArg t1 t3) *********)
(**************** and if g is a minimal unifier *********************)
(**************** of (Subst f t2) and (Subst f  t4) ******************)
(******** then [x:var](Subst g (f x)) is also a minimal unifier *********)
(*********** of (ConsArg t1 t2) and (ConsArg t3 t4) : ***************)
(*****************************************************************)

Hint Resolve over_comp under_comp.

Goal
forall (t1 t2 t3 t4 : quasiterm) (f g : quasisubst),
unif f t1 t3 ->
idempotent f ->
over f (ConsArg t1 t3) ->
under f (ConsArg t1 t3) ->
min_unif f t1 t3 ->
(forall l : list_nat,
 L_TERM l t1 -> L_TERM l t3 -> Length t1 = Length t3 :>nat -> term_subst l f) ->
unif g (Subst f t2) (Subst f t4) ->
idempotent g ->
over g (ConsArg (Subst f t2) (Subst f t4)) ->
under g (ConsArg (Subst f t2) (Subst f t4)) ->
min_unif g (Subst f t2) (Subst f t4) ->
(forall l : list_nat,
 L_TERM l (Subst f t2) ->
 L_TERM l (Subst f t4) ->
 Length (Subst f t2) = Length (Subst f t4) :>nat -> term_subst l g) ->
Unification (ConsArg t1 t2) (ConsArg t3 t4).
intros; apply Unif_succeed with (fun x : var => Subst g (f x)); intros;
 auto with arith.
(*apply unif_comp;over_comp;under_comp;min_unif_comp*)
apply (idempotent_Fondamental (ConsArg t2 t4)); auto with arith.
(*------------ Verifications on the terms:begin -------------*)
apply term_subst_comp with t1 t2 t3 t4; auto with arith.
(*------------ Verifications on the terms:end --------------*)
Save two_succes.

(*****************************************************************)
(************** If f is a minimal unifier of t1 and t3 ***************)
(*********** whose domain and image are in (ConsArg t1 t3) ********)
(*********************** and if the unification  *********************)
(***************** of (Subst f t2) and (Subst f  t4) fails *************)
(**** then the unification of (ConsArg t1 t2) and (ConsArg t3 t4) *****)
(**************************** fails also. ***************************)
(*****************************************************************)

Goal
forall (t1 t2 t3 t4 : quasiterm) (f : quasisubst),
unif f t1 t3 ->
idempotent f ->
min_unif f t1 t3 ->
(forall g : quasisubst,
 Subst g (Subst f t2) <> Subst g (Subst f t4) :>quasiterm)(*1*)
 -> Unification_f (ConsArg t1 t2) (ConsArg t3 t4).
unfold unif, idempotent, over, under, min_unif in |- *; intros;
 apply Unif_fail_def; intros.
unfold not in |- *; simpl in |- *; intros.
elim (H2 f0).
elim (H1 f0); unfold unif in |- *; intros.
(**)
elim (exp_comp_subst f f0 t2); elim (exp_comp_subst f f0 t4).
replace (Subst (fun x : var => Subst f0 (f x)) t2) with (Subst f0 t2).
replace (Subst (fun x : var => Subst f0 (f x)) t4) with (Subst f0 t4).
apply proj_ConsArg2 with (Subst f0 t1) (Subst f0 t3); auto with arith.
(**)
apply eq_restriction_s_t; intros.
elim (H4 x).
replace (Subst h (f x)) with (Subst h (Subst f (f x))).
elim (exp_comp_subst f h (f x)); apply eq_restriction_s_t; auto with arith. 
elim H0; auto with arith.
(**)
apply eq_restriction_s_t; intros.
elim (H4 x).
replace (Subst h (f x)) with (Subst h (Subst f (f x))).
elim (exp_comp_subst f h (f x)); apply eq_restriction_s_t; auto with arith. 
elim H0; auto with arith.
(**)
apply proj_ConsArg1 with (Subst f0 t2) (Subst f0 t4); auto with arith.
Save one_only_succes.

(*****************************************************************)
(*********** If t1 and t3 can be unified by the identity, **************)
(******** then (ConsArg t1 t2) and (ConsArg t3 t4) can this also *****) 
(**************** if and only if t2 and t4 can this . ****************)
(*****************************************************************)

Goal
forall (t1 t2 t3 t4 : quasiterm) (f : quasisubst),
(forall x : var, V x = f x :>quasiterm) ->
unif f t1 t3 ->
Unification t2 t4 -> Unification (ConsArg t1 t2) (ConsArg t3 t4).
unfold unif in |- *; intros.
Elimunif H1; unfold unif, over, under, idempotent, min_unif in |- *; intros.
(*Success*)
apply two_succes with f f0; replace (Subst f t2) with t2;
 replace (Subst f t4) with t4;
 unfold unif, over, under, idempotent, dom in |- *; 
 simpl in |- *; auto with arith.
(*apply eq_V_stab*)
intros; absurd (V y = f y :>quasiterm); auto with arith.
unfold min_unif in |- *; intros.
apply less_subst_init with g.
intros; elim (H x); auto with arith.
(*------------ Verifications on the terms:begin -------------*)
(**)intros; apply term_subst_init; intros; apply term_init; 
     (**)elim H; simpl in |- *; auto with arith.
(*------------ Verifications on the terms:end --------------*)
(*Fail*)
apply Unif_fail_def.
simpl in |- *; intros; unfold not in |- *; intros.
elim (n f0); apply proj_ConsArg2 with (Subst f0 t1) (Subst f0 t3);
 auto with arith.
Save eq_V_stab3.

(*****************************************************************)
(******************** For any terms u1 and u2, *******************)
(********** either there exists a minimal unifier of u1 and u2 ********)
(*********** whose domain and image are in (ConsArg u1 u2) *******)
(************** or u1 and u2 do not admit any unifier. *************)
(*****************************************************************)

Goal
forall (n : nat) (u1 u2 : quasiterm),
DIFFELNB (list_var (ConsArg u1 u2)) n -> Unification u1 u2.
intros n; pattern n in |- *; apply (ind_leS n).


   (***************************************************************)
   (********************* Case without variable : ********************)
   (***************************************************************)
intros; apply Unif_DIFFELNB_O; auto with arith.
   (***************************************************************)
   (************** Case with p+1 different variables, *******************)
   (**************** induction on u1, then on u2 : *********************)
   (***************************************************************)
simple induction u1; auto with arith. (*apply UnifV1;UnifC1*)
(*Case u1 = (Root ...) : *)
simple induction u2; auto with arith. (*apply UnifV2;UnifC2;UnifRoot;Decomp_fail;Fail_hd6*)
(*Case u1 = (ConsArg ...) : *)
simple induction u2; auto with arith. (*apply UnifV2;UnifC2;Decomp_fail;Fail_hd5*)
intros.
   (**      1 subgoal                                                *)
   (**      (Unification (ConsArg q q0) (ConsArg q1 q2))              *)
   (**       ============================            *)
   (**      number of different variables in (ConsArg q q1) :           *)
elim (DIFFELNBor (list_var (ConsArg q q1))); intros p0 H5.

   (***************************************************************)
   (******** Comparison of this number named p0 with p+1, **********)
   (*********** one knows that p0 < p+1 or p0 = p+1 : *************)
   (***************************************************************)
elim (DIFFELNB_ConsArg_ConsArg13_le q q0 q1 q2 (S p) H4 p0 H5); intros.
   (******************************************************************)
   (*  DIFFELNB_ConsArg_ConsArg13_le:(t1,t2,t3,t4:quasiterm)(n:nat)      *)
   (*(DIFFELNB (list_var (ConsArg (ConsArg t1 t2) (ConsArg t3 t4))) n) *)
   (*      ->(n0:nat)(DIFFELNB (list_var (ConsArg t1 t3)) n0          *)
   (*               ->({(le (S n0) n)}+{<nat>n0=n})                 *)
   (******************************************************************)

   (***************************************************************)
   (***************************************************************)
   (************************ Case p0 < p+1. **********************)
   (***************************************************************)
   (***************************************************************)

   (***************************************************************)
   (*********** one applies the recurrence hypothesis H : *************)
   (* (q:nat)(le q p)->(u1,u2:quasiterm)                              *)
   (* (DIFFELNB (list_var (ConsArg u1 u2)) q)->(Unification u1 u2)  *)
   (***************************************************************)
Elimunif (H p0 (le_S_n p0 p a) q q1 H5); intros.
2: auto with arith.
(*apply UnifConsArgfail1*)

   (***************************************************************)
   (******** the unifier f of f and y1 is either the identity, ***********) 
   (***************** or different of the identity : *******************)
   (***************************************************************)
elim (ident_or_notS (ConsArg q q1) f o); intros.

   (***************************************************************)
   (************************ Case f non identity ********************)
   (***************************************************************)
elim a0; intros x H6.

   (***************************************************************)
   (********* one supposes (Unification (Subst f q0) (Subst f q2)) ******)
   (***************************************************************)
cut (Unification (Subst f q0) (Subst f q2)).
intros H7; Elimunif H7; intros.
apply two_succes with f f0; auto with arith.
apply one_only_succes with f; auto with arith.

   (***************************************************************)
   (********* proof of (Unification (Subst f q0) (Subst f q2)) : *********)
   (********* 1) (list_var (ConsArg (Subst f q0) (Subst f q2))) *********)
   (******************** counts x1 different variables, ****************)
   (********** 2) one applies the recurrence hypothesis H *************)
   (********** 3) for this, one uses the fact that the unifier f *********)
   (********** makes the number of different variables decreasing. ******)
   (***************************************************************)
elim (DIFFELNBor (list_var (ConsArg (Subst f q0) (Subst f q2))));
 intros p1 H7.
apply (H p1); auto with arith.
apply le_S_n; apply (f_n_id_minus q q0 q1 q2 (S p)) with f; auto with arith.
   (****************************************************************)
   (***** f_n_id_minus:(t1,t2,t3,t4:quasiterm)(n:nat) *********************)
   (* (DIFFELNB **************************************************)
   (*** (list_var (ConsArg (ConsArg t1 t2) (ConsArg t3 t4))) n) ********)
   (* ->(f:quasisubst)(idempotent f)->(over f (ConsArg t1 t3)) ********)
   (* ->(under f (ConsArg t1 t3)) **********************************)
   (* ->((Ex [x:var](~<quasiterm>(V x)=(f x)))) ****************)
   (* ->(n0:nat)(DIFFELNB  **************************************)
   (*********** (list_var (ConsArg (Subst f t2) (Subst f t4))) n0) *******)
   (* ->(le (S n0) n) **********************************************)
   (****************************************************************)
exists x; auto with arith.

   (****************************************************************)
   (**************** Case f = identity extentionnelly ******************)
   (** 1) eq_V_stab3 reduces the problem to (Unification q0 q2), **********)
   (** 2) (list_var (ConsArg q0 q2)) counts p0 different variables, ********)
   (***** 3) si p0 < p+1, one applies the recurrence hypothesis H *******)
   (***** 4) si p0 = p+1, one applies the recurrence hypothesis H1. *****)
   (****************************************************************)
apply eq_V_stab3 with f; auto with arith.
elim (DIFFELNBor (list_var (ConsArg q0 q2))); intros p1 H6.
elim (DIFFELNB_ConsArg_ConsArg24_le q q0 q1 q2 (S p) H4 p1 H6); intros.
   (***************************************************************)
   (* DIFFELNB_ConsArg_ConsArg24_le:(t1,t2,t3,t4:quasiterm)(n:nat) ****)
   (* (DIFFELNB *************************************************)
   (* ***(list_var (ConsArg (ConsArg t1 t2) (ConsArg t3 t4))) n) ******)
   (* ->(n0:nat)(DIFFELNB (list_var (ConsArg t2 t4)) n0) ***********)
   (* ->({(le (S n0) n)}+{<nat>n0=n}) ****************************)
   (***************************************************************)
apply (H p1 (le_S_n p1 p a0) q0 q2); auto with arith.
apply (H1 q2); elim b0; auto with arith.

   (***************************************************************)
   (***************************************************************)
   (********************* Case p0 = p+1 **************************)
   (***************************************************************)
   (***************************************************************)

   (***************************************************************)
   (******** 1) one applies the recurrence hypothesis H0 **************)
   (********** which proves (Unification y y1), **********************)
   (********2) one proceeds after exactly like above. ******************)
   (***************************************************************)
cut (Unification q q1); [ intro H0' | apply (H0 q1); elim b; auto with arith ].
Elimunif H0'; auto with arith; intros. (*apply UnifConsArgfail1*)
elim (ident_or_notS (ConsArg q q1) f o); intros.
elim a; intros x H6.

   (***************************************************************)
   (********* one supposes (Unification (Subst f q0) (Subst f q2))******)
   (***************************************************************)
cut (Unification (Subst f q0) (Subst f q2)).
intros H7; Elimunif H7; intros.
apply two_succes with f f0; auto with arith.
apply one_only_succes with f; auto with arith.

   (***************************************************************)
elim (DIFFELNBor (list_var (ConsArg (Subst f q0) (Subst f q2))));
 intros p1 H7.
apply (H p1); auto with arith.
apply le_S_n; apply (f_n_id_minus q q0 q1 q2 (S p)) with f; auto with arith.
exists x; auto with arith.

   (***************************************************************)
apply eq_V_stab3 with f; auto with arith.
elim (DIFFELNBor (list_var (ConsArg q0 q2))); intros p1 H6.
elim (DIFFELNB_ConsArg_ConsArg24_le q q0 q1 q2 (S p) H4 p1 H6); intros.
apply (H p1); auto with arith. (*apply le_S_n*)
apply (H1 q2); elim b1; auto with arith.
Save proof_unif.

Goal forall t u : quasiterm, Unification t u.
intros; elim (DIFFELNBor (list_var (ConsArg t u))); intros n0 p;
 apply proof_unif with n0; auto with arith.
Save unif_proof.

End algorithmes.

Goal forall t u : quasiterm, Unification_or_fail t u.
  intros; apply Unification_build with (Unification_f t u) t u.
    apply unif_proof. intro c; apply Unification_or_fail_fail; exact c.
    intro c; exact c.
    intro res; apply Unification_or_fail_succeed; exact res.
Save unif_call.
