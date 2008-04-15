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
(*                         nat_term_eq_quasiterm.v                          *)
(****************************************************************************)

Require Import Arith.
Require Import nat_complements.

(*---------------------------------------------*)
(*------------ Verifications on the terms:begin -------------*)
(*---------------------------------------------*)

Section nat_sequence.

Inductive list_nat : Set :=
  | nil_nat : list_nat
  | cons_nat : nat -> list_nat -> list_nat.

Fixpoint At_last (x : nat) (l : list_nat) {struct l} : list_nat :=
  match l return list_nat with
  | nil_nat =>
      (* nil_nat *) cons_nat x nil_nat
      (* cons_nat c ll *)
  | cons_nat c ll => cons_nat c (At_last x ll)
  end.


Fixpoint List_queue_nat (l : list_nat) : list_nat :=
  match l return list_nat with
  | nil_nat =>
      (* nil_nat *) nil_nat
      (* cons_nat c ll *)
  | cons_nat c tail => At_last c (List_queue_nat tail)
  end.




Fixpoint Constr_f (l : list_nat) : nat -> nat :=
  fun n : nat =>
  match l return nat with
  | nil_nat =>
      (* nil_nat *) 0
  | cons_nat m tail =>
      match n return nat with
      | O =>
          (* O *)  m
          (* (S p) *)
      | S p => Constr_f tail p
      end
  end.

(***********************************************************************)
(********************** Properties of  Constr_f ***************************)
(***********************************************************************)

Inductive OK_Constr_f (f : list_nat -> nat -> nat) : Prop :=
    OK_Constr_f_init :
      (forall x : nat, 0 = f nil_nat x :>nat) ->
      (forall (val : nat) (l : list_nat), val = f (cons_nat val l) 0 :>nat) ->
      (forall (x val : nat) (l : list_nat),
       f l x = f (cons_nat val l) (S x) :>nat) -> OK_Constr_f f.

Lemma Constr_f_OK : OK_Constr_f Constr_f.
apply OK_Constr_f_init; simpl in |- *; auto; simple induction x;
 simpl in |- *; auto.
Qed.

Inductive OK_At_last (f : nat -> list_nat -> list_nat) : Prop :=
    OK_At_last_init :
      (forall x : nat, cons_nat x nil_nat = f x nil_nat :>list_nat) ->
      (forall x y : nat,
       cons_nat y (cons_nat x nil_nat) = f x (f y nil_nat) :>list_nat) ->
      OK_At_last f.

Lemma At_last_OK : OK_At_last At_last.
apply OK_At_last_init; simpl in |- *; auto.
Qed.

Inductive OK_List_queue_nat (f : list_nat -> list_nat) : Prop :=
    OK_List_queue_nat_init :
      nil_nat = f nil_nat :>list_nat ->
      (forall (x : nat) (l : list_nat),
       At_last x (f l) = f (cons_nat x l) :>list_nat) -> 
      OK_List_queue_nat f.

Lemma List_queue_nat_OK : OK_List_queue_nat List_queue_nat.
apply OK_List_queue_nat_init; simpl in |- *; auto.
Qed.

End nat_sequence.

(**********************************************************************)
(******************* Specifications of terms ******************************)
(**********************************************************************)

Section terms.

Definition fun_ : Set := nat.

Definition var : Set := nat.

Lemma var_eq_decP : forall x x0 : var, x = x0 :>var \/ x <> x0.
intros; elim (nat_eq_decP x x0); auto.
Qed.

Lemma var_eq_decS : forall x x0 : var, {x = x0 :>var} + {x <> x0}.
intros; elim (nat_eq_decS x x0); auto.
Qed.

Lemma fun_eq_decP : forall x x0 : fun_, x = x0 :>fun_ \/ x <> x0.
intros; elim (nat_eq_decP x x0); auto.
Qed.

Lemma fun_eq_decS : forall x x0 : fun_, {x = x0 :>fun_} + {x <> x0}.
intros; elim (nat_eq_decS x x0); auto.
Qed.

 
Inductive quasiterm : Set :=
  | V : var -> quasiterm (*variable quasiterm*)
  | C : fun_ -> quasiterm (*constant quasiterm*)
  | Root : fun_ -> quasiterm -> quasiterm (*rooting*)
  | ConsArg : quasiterm -> quasiterm -> quasiterm.
                                 (*building the pairs of quasiterms*)

(**********************************************************************)
(*********************** The arity function *****************************)
(**********************************************************************)

Hypothesis list_arity : list_nat.

Definition arity : fun_ -> nat := Constr_f (List_queue_nat list_arity).

(**********************************************************************)
(********************** Length of a quasiterm ***************************)
(**********************************************************************)




Fixpoint Length (t : quasiterm) : nat :=
  match t return nat with
  | V x => 1
  | C f => 1
  | Root f u => 1
  | ConsArg t1 t2 =>
      Length t1 + Length t2
      (*(<nat>Match (Length t1) with (Length t2) [x:nat]S end)*)
  end.


(***********************************************************************)
(********************** Predicate SIMPLE *******************************)
(****** Simple term is constant term or variable term or rooted term. *******)
(***********************************************************************)

Definition SIMPLE (t : quasiterm) : Prop :=
  match t return Prop with
  | V x => True
  | C l => True
  | Root l u => True
  | ConsArg t1 t2 => False
  end.

(***********************************************************************)
(***************** Predicates l_term and L_TERM : ***********************)
(***********************************************************************)

Inductive l_term : quasiterm -> Prop :=
  | l_term_initV : forall x : var, l_term (V x)
  | l_term_initC : forall f : fun_, 0 = arity f :>nat -> l_term (C f)
  | l_term_Root :
      forall (f : fun_) (t : quasiterm),
      l_term t -> arity f = Length t :>nat -> l_term (Root f t)
  | l_term_ConsArg :
      forall t1 t2 : quasiterm,
      l_term t1 -> l_term t2 -> SIMPLE t1 -> l_term (ConsArg t1 t2).

Fixpoint L_TERM (t : quasiterm) : Prop :=
  match t return Prop with
  | V x => True
  | C c => 0 = arity c
  | Root l t => L_TERM t /\ arity l = Length t
  | ConsArg t1 t2 => SIMPLE t1 /\ L_TERM t1 /\ L_TERM t2
  end.

(***********************************************************************)
(******************** L_TERM is equivalent to l_term : *******************)
(***********************************************************************)

Lemma L_TERM_l_term : forall t : quasiterm, L_TERM t -> l_term t.
intro; elim t; simpl in |- *; intros.
apply l_term_initV; auto.
apply l_term_initC; auto.
apply l_term_Root.
apply H; elim H0; auto.
elim H0; auto.
apply l_term_ConsArg.
apply H; elim H1; intros H2 H3; elim H3; intros; auto.
apply H0; elim H1; intros H2 H3; elim H3; intros; auto.
elim H1; auto.
Qed.

Lemma l_term_L_TERM : forall t : quasiterm, l_term t -> L_TERM t.
intros; elim H; simpl in |- *; auto.
Qed.

(***********************************************************************)
(******************** Predicate term : ***********************************)
(***********************************************************************)

Inductive term (t : quasiterm) : Prop :=
    term_init : L_TERM t -> SIMPLE t -> term t.

(***********************************************************************)
(************ Decidability of L_TERM and decidability of term : ************)
(***********************************************************************)

Lemma SIMPLE_decS : forall t : quasiterm, {SIMPLE t} + {~ SIMPLE t}.
intros; elim t; simpl in |- *; auto.
Qed.

Lemma L_TERM_decS : forall t : quasiterm, {L_TERM t} + {~ L_TERM t}.
simple induction t; simpl in |- *; auto.
intros f; elim (nat_eq_decS 0 (arity f)); intros; simpl in |- *; auto.
intros f y h0; elim (nat_eq_decS (arity f) (Length y)); intros h.
elim h; elim h0; intros; auto.
right; tauto.

right; tauto.

intros y h y0 h0; elim h; intros.
elim h0; intros.
elim (SIMPLE_decS y); intros h1.
auto.
right; tauto.
right; tauto.
right; tauto.
Qed.

Lemma term_decS : forall t : quasiterm, {term t} + {~ term t}.
intro; elim (L_TERM_decS t); intros h1; elim (SIMPLE_decS t); intros h2.
left; apply term_init; auto.
right; unfold not in |- *; intros h3; elim h2; elim h3; intros; auto.
right; unfold not in |- *; intros h3; elim h1; elim h3; intros; auto.
right; unfold not in |- *; intros h3; elim h1; elim h3; intros; auto.
Qed.

(***********************************************************************)
(******************* Properties of  Length *******************************)
(***********************************************************************)

Lemma Length_n_O : forall t : quasiterm, {x : nat | Length t = S x}.
simple induction t.
exists 0; simpl in |- *; auto.
exists 0; simpl in |- *; auto.
exists 0; simpl in |- *; auto.
intros qx Hqx qy Hqy.
elim Hqy; elim Hqx; intros x Eqx y Eqy.
exists (x + Length qy).
simpl in |- *.
rewrite Eqx; auto.
Qed.
 
Lemma n_SO_Length_ConsArg :
 forall t t0 : quasiterm, 1 <> Length (ConsArg t t0).
intros; elim (Length_n_O t); elim (Length_n_O t0); intros; simpl in |- *.
replace (Length t) with (S x0); replace (Length t0) with (S x).
elim x0; simpl in |- *.
discriminate.
intros; discriminate.
Qed.

Lemma SIMPLE_SO : forall t : quasiterm, SIMPLE t -> 1 = Length t :>nat.
simple induction t; simpl in |- *; intros; auto.
absurd False; auto.
Qed.

Lemma Length_SO_term :
 forall t : quasiterm, L_TERM t -> 1 = Length t :>nat -> term t.
simple induction t; intros; apply term_init; simpl in |- *; auto.
apply (n_SO_Length_ConsArg q q0); auto.
Qed.

Lemma term_L_TERM_Length :
 forall t : quasiterm, term t -> L_TERM t /\ 1 = Length t :>nat.
simple induction t.
intros; simpl in |- *; auto.
intros; simpl in |- *.
split; auto.
elim H; simpl in |- *; intros h; elim h; auto.
simpl in |- *; intros.
split; auto.
elim H0; simpl in |- *; intros h; elim h; intros; split; auto.
simpl in |- *; intros.
split.
elim H1; simpl in |- *; intros; auto.
elim H1; simpl in |- *; intros.
absurd False; auto.
Qed.

End terms.

Section eq_quasiterm.

(***********************************************************************)
(************************ Structural predicates ***************************)
(***********************************************************************)

Definition BC (t : quasiterm) : Prop :=
  match t return Prop with
  | V _ => False
  | C _ => True
  | Root _ _ => False
  | ConsArg _ t2 => False
  end.

Definition BV (t : quasiterm) : Prop :=
  match t return Prop with
  | V _ => True
  | C _ => False
  | Root _ _ => False
  | ConsArg _ t2 => False
  end.

Definition BRoot (t : quasiterm) : Prop :=
  match t return Prop with
  | V _ => False
  | C _ => False
  | Root _ _ => True
  | ConsArg _ t2 => False
  end.

Definition BConsArg (t : quasiterm) : Prop :=
  match t return Prop with
  | V _ => False
  | C _ => False
  | Root _ _ => False
  | ConsArg _ t2 => True
  end.

(***********************************************************************)
(********************** Destroyers (Destructors): *************************)
(***********************************************************************)
Definition Destr1 (t : quasiterm) :=
  match t return quasiterm with
  | V x => V x
  | C x => C x
  | Root _ p => p
  | ConsArg p _ => p
  end.

Definition Destr2 (t : quasiterm) :=
  match t return quasiterm with
  | V x => V x
  | C x => C x
  | Root _ p => p
  | ConsArg _ q => q
  end.

Definition Destrvar (X : var) (t : quasiterm) :=
  match t return var with
  | V x => x
  | C _ => X
  | Root _ _ => X
  | ConsArg _ _ => X
  end.


Definition Destrfun (F : fun_) (t : quasiterm) :=
  match t return fun_ with
  | V _ => F
  | C l => l
  | Root l _ => l
  | ConsArg p q => F
  end.

(**********************************************************************)
(******************** Equal in the Set of quasiterms : *******************)
(**********************************************************************)

Lemma proj_C : forall l1 l2 : fun_, C l1 = C l2 :>quasiterm -> l1 = l2 :>fun_.
intros; replace l1 with (Destrfun l1 (C l1)); auto.
replace l2 with (Destrfun l1 (C l2)); auto.
elim H; auto.
Qed.

Lemma proj_V : forall x1 x2 : var, V x1 = V x2 :>quasiterm -> x1 = x2 :>var.
intros; replace x1 with (Destrvar x1 (V x1)); auto.
replace x2 with (Destrvar x1 (V x2)); auto.
elim H; auto.
Qed.

Lemma proj_Root1 :
 forall (t1 t2 : quasiterm) (l1 l2 : fun_),
 Root l1 t1 = Root l2 t2 :>quasiterm -> l1 = l2 :>fun_.
intros; replace l1 with (Destrfun l1 (Root l1 t1)); auto.
replace l2 with (Destrfun l1 (Root l2 t2)); auto.
elim H; auto.
Qed.

Lemma proj_Root2 :
 forall (t1 t2 : quasiterm) (l1 l2 : fun_),
 Root l1 t1 = Root l2 t2 :>quasiterm -> t1 = t2 :>quasiterm.
intros; replace t1 with (Destr1 (Root l1 t1)); auto.
replace t2 with (Destr2 (Root l2 t2)); auto.
elim H; auto.
Qed.

Lemma proj_ConsArg1 :
 forall t1 t2 t3 t4 : quasiterm,
 ConsArg t1 t2 = ConsArg t3 t4 :>quasiterm -> t1 = t3 :>quasiterm.
intros; replace t1 with (Destr1 (ConsArg t1 t2)); auto.
replace t3 with (Destr1 (ConsArg t3 t4)); auto.
elim H; auto.
Qed.

Lemma proj_ConsArg2 :
 forall t1 t2 t3 t4 : quasiterm,
 ConsArg t1 t2 = ConsArg t3 t4 :>quasiterm -> t2 = t4 :>quasiterm.
intros; replace t2 with (Destr2 (ConsArg t1 t2)); auto.
replace t4 with (Destr2 (ConsArg t3 t4)); auto.
elim H; auto.
Qed.

(**********************************************************************)
(****************** Not equal in the Set of the quasiterms : **************)
(**********************************************************************)
Lemma C_diff_C : forall l l0 : fun_, l <> l0 -> C l <> C l0 :>quasiterm.
unfold not in |- *; intros; elim H; apply proj_C; auto.
Qed.

Lemma V_diff_V : forall x y : var, x <> y :>var -> V x <> V y :>quasiterm.
unfold not in |- *; intros; elim H; apply proj_V; auto.
Qed.

Lemma ConsArg_diff_ConsArg :
 forall t t0 t1 t2 : quasiterm,
 t <> t1 :>quasiterm \/ t0 <> t2 :>quasiterm ->
 ConsArg t t0 <> ConsArg t1 t2 :>quasiterm.
unfold not in |- *; intros; elim H; intros; elim H1.
apply proj_ConsArg1 with t0 t2; auto.
apply proj_ConsArg2 with t t1; auto.
Qed.

Lemma Root_diff_Root :
 forall (l l0 : fun_) (t t0 : quasiterm),
 l <> l0 :>fun_ \/ t <> t0 :>quasiterm -> Root l t <> Root l0 t0 :>quasiterm.
unfold not in |- *; intros; elim H; intros; elim H1.
apply proj_Root1 with t t0; auto.
apply proj_Root2 with l l0; auto.
Qed.

(**********************************************************************)
(*********** Decidability of the equality in the Set of quasiterms : *********)
(**********************************************************************)
Lemma quasiterm_eq_decS :
 forall t t0 : quasiterm, {t = t0 :>quasiterm} + {t <> t0 :>quasiterm}.
simple induction t.
simple induction t0.
(*t=(V ...)*)
intros; elim (var_eq_decS v v0); intros H.
elim H; auto.
right; apply V_diff_V; auto.
intros; right; apply (Diff quasiterm BV); simpl in |- *; auto.
intros; right; apply (Diff quasiterm BV); simpl in |- *; auto.
intros; right; apply (Diff quasiterm BV); simpl in |- *; auto.
(*t=(C ...)*)
simple induction t0.
intros; right; apply (Diff quasiterm BC); simpl in |- *; auto.
intros; elim (fun_eq_decS f f0); intros H.
elim H; auto.
right; apply C_diff_C; auto.
intros; right; apply (Diff quasiterm BC); simpl in |- *; auto.
intros; right; apply (Diff quasiterm BC); simpl in |- *; auto.
(*t=(Root...)*)
simple induction t0.
intros; right; apply (Diff quasiterm BRoot); simpl in |- *; auto.
intros; right; apply (Diff quasiterm BRoot); simpl in |- *; auto.
intros.
elim (H q0); intros y.
rewrite y; elim (fun_eq_decS f f0); intros y0.
rewrite y0; auto.
right; simplify_eq; auto.
right; simplify_eq; auto.
intros; right; simplify_eq.
(*t=(ConsArg ...)*)
simple induction t0.
intros; right; simplify_eq.
intros; right; simplify_eq.
intros; right; simplify_eq.
intros y1 H1 y2 H2.
elim (H y1); intros E1.
elim (H0 y2); intros E2.
rewrite E1; rewrite E2; auto.
right; simplify_eq; tauto.
right; simplify_eq; tauto.
Qed.

Lemma quasiterm_eq_decP :
 forall t t0 : quasiterm, t = t0 :>quasiterm \/ t <> t0.
intros; elim (quasiterm_eq_decS t t0); intros; auto.
Qed.

(**********************************************************************)
(********************* End of equality in quasiterm **********************)
(**********************************************************************)


(***********************************************************************)
(************************* End eq_quasiterm. ***************************)
(***********************************************************************)
End eq_quasiterm.