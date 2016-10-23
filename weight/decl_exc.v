(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(* Jean-Francois.Monin@lannion.cnet.fr                                      *)
(* August 1994, Coq V5.8.3                                                  *)
(*                                                                          *)
(****************************************************************************)
(*                                decl_exc.v                                *)
(****************************************************************************)

(* 
  Declaration of exceptions.
  To be used by cps_mcont.v
*)

(* 2 levels of exception *)
Inductive Txlev : Set :=
  | xl1 : Txlev
  | xl2 : Txlev.

(* The first level carries no value, the second carries a boolean *)
Inductive Txval : Txlev -> Set :=
  | xv1 : Txval xl1
  | xv2 : bool -> Txval xl2.

Ltac AutoTx :=
  intro l; elim l; simpl in |- *; intros v Hv; elim Hv; auto with v62.

Section inverse_of_xv2.

Theorem xl2_bool : Txval xl2 -> bool.
intro x; elim x.
  exact false. (* irrelevant *)
  intro b; exact b.
Defined.

(* 
  This section aims at proving :
  (v:(Txval xl2)) v=(xv2 (xl2_bool v).
*)

(* Pitfall : do not use this simpler version of l_xl2.
Goal (l:Txlev) l=xl2 ->(Txval l)->(Txval xl2).
  Intros l E v.
  Elim E; Exact v.
Save l_xl2.
*)

Theorem l_xl2 : forall l : Txlev, l = xl2 -> Txval l -> Txval xl2.
simple induction l.
  intro E; discriminate E.
  intros e v; exact v.
Defined.

Theorem inv_xv2_xl2_bool_aux :
 forall (l : Txlev) (v : Txval l) (e : l = xl2),
 l_xl2 l e v = xv2 (xl2_bool (l_xl2 l e v)).
simple induction v.
  intros; absurd (xl1 = xl2); [ discriminate | assumption ].
  auto.
Qed.

Theorem inv_xv2_xl2_bool : forall v : Txval xl2, v = xv2 (xl2_bool v).
  intro v.
  cut (xl2 = xl2); [ intro e | auto ].
  cut (l_xl2 xl2 e v = v); [ intro e'; elim e' | auto ].
  apply inv_xv2_xl2_bool_aux.
Qed.

End inverse_of_xv2.


Theorem noteq_xv2_true_false : xv2 true = xv2 false -> False.
  intro E; discriminate E.
Qed.

(* Hints Resolve noteq_xv2_true_false. *)