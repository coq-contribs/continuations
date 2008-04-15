(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(* Jean-Francois.Monin@lannion.cnet.fr                                      *)
(* December 1994, Coq V5.10                                                 *)
(*                                                                          *)
(****************************************************************************)
(*                                tree_plus.v                               *)
(****************************************************************************)

(* ================================================== *)

(* Require func_pred. *)

Require Export tree.

Definition leaveplus : tree -> nat := ext_morph plus.

Definition Pleaveplus : tree -> nat -> Prop := Pext_morph plus.

Definition Plp := Pl plus.
Definition Pnp := Pn plus.

Definition Plp_lp : forall t : tree, Pleaveplus t (leaveplus t) :=
  Pem_em plus. 
     
Definition lp_eq_Plp :
  forall (t : tree) (n : nat), n = leaveplus t -> Pleaveplus t n :=
  em_eq_Pem plus.

Definition Plp_lp_eq :
  forall (t : tree) (n : nat), Pleaveplus t n -> n = leaveplus t :=
  Pem_em_eq plus.



Hint Resolve Plp Pnp lp_eq_Plp Plp_lp_eq.


(* ================================================== *)
