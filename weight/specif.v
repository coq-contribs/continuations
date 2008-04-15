(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(* Jean-Francois.Monin@lannion.cnet.fr                                      *)
(* August 1994, Coq V5.8.3                                                  *)
(*                                                                          *)
(****************************************************************************)
(*                                 specif.v                                 *)
(****************************************************************************)

(* ======================================================= *)
(*             Specification and useful lemmas             *)
(* ======================================================= *)

Require Export Le.
Require Export tree_plus.
Require Export Plus.

(* le_plus_trans de la biblio std serait mieux appele le_plus_trans_left *)
Theorem le_plus_trans_right : forall n m p : nat, n <= p -> n <= m + p.
intros; elim plus_comm; auto with v62.
Qed.
(* Hints Resolve le_plus_trans_right. *)

(* ======================================================= *)

Theorem Leibniz_endo :
 forall (S : Set) (f : S -> S) (n m : S), n = m -> f n = f m.
intros S f n m E; elim E; auto with v62.
Qed.
(* Hints Resolve Leibniz_endo. *)

(* ======================================================= *)
(* The first specification *)

Inductive P_overweight (m : nat) (t : tree) : Prop :=
    deb_base : m <= leaveplus t -> P_overweight m t.
Hint Resolve deb_base.
Hint Unfold leaveplus.


Inductive SPEC (m : nat) (t : tree) : bool -> Prop :=
  | St : P_overweight m t -> SPEC m t true
  | Sf : ~ P_overweight m t -> SPEC m t false.
Hint Resolve St Sf.

Theorem other_Sf :
 forall (m n : nat) (t : tree),
 n = leaveplus t -> ~ m <= n -> ~ P_overweight m t.
unfold not in |- *; intros m n t Heg Nle_mn Hdeb; elim Hdeb; elim Heg;
 auto with v62.
Qed.

Theorem yet_another_Sf :
 forall (m : nat) (t : tree), ~ m <= leaveplus t -> ~ P_overweight m t.
unfold not in |- *; intros m t Nle_mt Hdeb; elim Hdeb; auto with v62.
Qed.

Hint Resolve yet_another_Sf.


(* Type of the final result in the simplest case *)

Inductive RESU (m : nat) (t : tree) : Set :=
    exres : forall b : bool, SPEC m t b -> RESU m t.

(* ------------------------------------------------------- *)
(* Specification et lemmes afferents pour l'extraction *)
(* Avec levee d'exception *)

(* acceleration de la levee d'exception via une somme cumulee *)

Inductive condsum_accu (m a : nat) (t : tree) : Set :=
    condsum_accu_intro :
      forall n : nat, n = a + leaveplus t -> ~ m <= n -> condsum_accu m a t.

Definition P_overweight_accu (m a : nat) (t : tree) := m <= a + leaveplus t.

Theorem deb_accu_plus_r :
 forall (m a b : nat) (t : tree),
 P_overweight_accu m a t -> P_overweight_accu m (a + b) t.
unfold P_overweight_accu in |- *.
intros m a b t Hlemt.
apply le_trans with (a + leaveplus t); auto with v62.
Qed.
Hint Resolve deb_accu_plus_r.

Theorem deb_left_accu_plus :
 forall (m a : nat) (t1 t2 : tree),
 P_overweight_accu m (a + leaveplus t2) t1 ->
 P_overweight_accu m a (node t1 t2).
unfold P_overweight_accu in |- *.
intros m a t1 t2; simpl in |- *.
pattern (leaveplus t1 + leaveplus t2) in |- *; elim plus_comm;
 elim plus_assoc_reverse; auto with v62.
Qed.
Theorem deb_right_accu_plus :
 forall (m a : nat) (t1 t2 : tree),
 P_overweight_accu m (a + leaveplus t1) t2 ->
 P_overweight_accu m a (node t1 t2).
unfold P_overweight_accu in |- *.
intros m a t1 t2; elim plus_assoc; intro Hlemt2.
simpl in |- *; auto with v62.
Qed.

(* Hints Resolve deb_left_accu_plus deb_right_accu_plus. *)

(* ============================================================== *)

(*
   Pgm avec 2 exceptions de niveaux differents
*)

Section lists.
Variable A : Set.

Inductive list : Set :=
  | nil : list
  | cons : A -> list -> list.
End lists.

Definition lbool := list bool.
Definition ltree := list tree.
Definition nilb := nil bool.
Definition nilt := nil tree.
Definition consb := cons bool.
Definition const := cons tree.

Inductive Texc : Set :=
    x_zer : Texc.


Inductive lboolexc : Set :=
  | exc_lb : lboolexc
  | some_lb : lbool -> lboolexc.


(* -------------------------------------- *)
Inductive Pposs_zer : tree -> Prop :=
  | pz_base : Pposs_zer (leaf 0)
  | pz_left : forall t1 t2 : tree, Pposs_zer t1 -> Pposs_zer (node t1 t2)
  | pz_right : forall t1 t2 : tree, Pposs_zer t2 -> Pposs_zer (node t1 t2).
Hint Resolve pz_base pz_left pz_right.


Theorem inv_pz_0 : forall n : nat, Pposs_zer (leaf n) -> 0 = n.
intros n Hposs; inversion_clear Hposs; auto with v62.
Qed.
(* Hints Resolve inv_pz_0. *)


Theorem inv_pz_node :
 forall t1 t2 : tree, Pposs_zer (node t1 t2) -> Pposs_zer t1 \/ Pposs_zer t2.
intros t1 t2 Hpz; inversion_clear Hpz; auto with v62.
Qed.
(* Hints Resolve inv_pz_node. *)

Theorem not_pz_node :
 forall t1 t2 : tree,
 ~ Pposs_zer t1 -> ~ Pposs_zer t2 -> ~ Pposs_zer (node t1 t2).
intros t1 t2 Hnpz1 Hnpz2.
unfold not in |- *; intro Hpz; inversion_clear Hpz; auto with v62.
Qed.

(* Hints Resolve not_pz_node. *)



(* -------------------------------------- *)

Inductive boolexc : Set :=
  | exc_b : boolexc
  | some_b : bool -> boolexc.

(* Remarque : non determinisme entre Se2 et St2 *)
Inductive SPEC2 (m : nat) (t : tree) : boolexc -> Prop :=
  | Se2 : Pposs_zer t -> SPEC2 m t exc_b
  | St2 : m <= leaveplus t -> SPEC2 m t (some_b true)
  | Sf2 : ~ m <= leaveplus t -> SPEC2 m t (some_b false).
Hint Resolve Se2 St2 Sf2.

Inductive RESU2 (m : nat) (t : tree) : Set :=
    cR2 : forall r : boolexc, SPEC2 m t r -> RESU2 m t.


(* -------------------------------------- *)
Inductive Pposs_zerl : ltree -> Prop :=
  | base_zerl :
      forall t : tree,
      Pposs_zer t -> forall lt : ltree, Pposs_zerl (const t lt)
  | rec_zerl :
      forall lt : ltree,
      Pposs_zerl lt -> forall t : tree, Pposs_zerl (const t lt).
Hint Resolve base_zerl rec_zerl.

 
Theorem inv_poss_zerl :
 forall (t : tree) (lt : ltree),
 Pposs_zerl (const t lt) -> Pposs_zer t \/ Pposs_zerl lt.
intros t lt Hpzl. 
simple inversion Hpzl; unfold const in H0; injection H0; intros El Et;
 elim El; elim Et; auto with v62.
Qed.
(* Hints Resolve inv_poss_zerl. *)

Theorem inv_poss_zerl_nil : ~ Pposs_zerl nilt.
unfold not in |- *; intro Hpzn.
simple inversion Hpzn; unfold const, nilt in H0; simplify_eq H0.
Qed.
(* Hints Resolve inv_poss_zerl_nil. *)


Inductive SPECL (m : nat) : ltree -> lboolexc -> Prop :=
  | Snil : SPECL m nilt (some_lb nilb)
  | Selz : forall lt : ltree, Pposs_zerl lt -> SPECL m lt exc_lb
  | Selt :
      forall t : tree,
      m <= leaveplus t ->
      forall (lt : ltree) (lb : lbool),
      SPECL m lt (some_lb lb) ->
      SPECL m (const t lt) (some_lb (consb true lb))
  | Self :
      forall t : tree,
      ~ m <= leaveplus t ->
      forall (lt : ltree) (lb : lbool),
      SPECL m lt (some_lb lb) ->
      SPECL m (const t lt) (some_lb (consb false lb)).
Hint Resolve Snil Selz Selt Self.

Inductive RESUL (m : nat) (lt : ltree) : Set :=
    cRL : forall lb : lboolexc, SPECL m lt lb -> RESUL m lt.

Inductive lcond (m : nat) (lt : ltree) : Set :=
    clc : forall lb : lbool, SPECL m lt (some_lb lb) -> lcond m lt.


(* ============================================================ *)