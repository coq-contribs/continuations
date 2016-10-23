(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(* Jean-Francois.Monin@lannion.cnet.fr                                      *)
(* December 1994, Coq V5.10                                                 *)
(*                                                                          *)
(****************************************************************************)
(*                                  tree.v                                  *)
(****************************************************************************)

Inductive tree : Set :=
  | leaf : nat -> tree
  | node : tree -> tree -> tree.

Section func_pred.

Variable bin : nat -> nat -> nat.

Fixpoint ext_morph (t : tree) : nat :=
  match t return nat with
  | leaf n => n
  | node t1 t2 => bin (ext_morph t1) (ext_morph t2)
  end.

Inductive Pext_morph : tree -> nat -> Prop :=
  | Pl : forall n : nat, Pext_morph (leaf n) n
  | Pn :
      forall (t1 t2 : tree) (n1 n2 : nat),
      Pext_morph t1 n1 ->
      Pext_morph t2 n2 -> Pext_morph (node t1 t2) (bin n1 n2).
Hint Resolve Pl Pn.

Theorem Pem_em : forall t : tree, Pext_morph t (ext_morph t).
simple induction t; simpl in |- *; auto.
Qed.

Theorem em_eq_Pem :
 forall (t : tree) (n : nat), n = ext_morph t -> Pext_morph t n.
intros t n Heq; rewrite Heq; apply Pem_em.
Qed.

Theorem Pem_em_eq :
 forall (t : tree) (n : nat), Pext_morph t n -> n = ext_morph t.
simple induction 1.
   auto.
   intros t1 t2 n1 n2 HPem1 Heq1 HPem2 Heq2.
      rewrite Heq1; rewrite Heq2; auto.
Qed.


End func_pred.

(* ============================== *)
