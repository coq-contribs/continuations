(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

Inductive color : Set :=
  | blue : color
  | red : color
  | yellow : color.


Inductive tree1 : Set :=
  | Leaf : nat -> tree1
  | Nd1 : color -> tree1 -> tree1.


Fixpoint def_cop (T : tree1) : tree1 :=
  match T with
  | Leaf n => Leaf n
  | Nd1 blue t => Nd1 red (def_cop t)
  | Nd1 red t => Nd1 red (def_cop t)
  | Nd1 yellow t => Nd1 yellow (def_cop t)
  end.

Require Import Mx_defs.

(* (Mx P A) computes an inhabitant of A but may raise an exception if P *)
Theorem core_cop :
 forall t : tree1,
 Mx (t = def_cop t) {t' : tree1 | t' = def_cop t &  t <> t'}.

fix 1.
intro t; case t; clear t.
  simpl in |- *; intros n. apply Mx_raise. trivial.

  intros c t1; case c; simpl in |- *; clear c.
    (* c = blue *)
    apply Mx_try with (1 := core_cop t1).
      intros (t', eg, di); apply Mx_unit. exists (Nd1 red t'); [ elim eg; trivial | simplify_eq ].

      intro eg; apply Mx_unit. exists (Nd1 red t1); [ elim eg; trivial | simplify_eq ].

    (* c = red *)
    apply Mx_bind with (1 := core_cop t1).
      intros (t', eg, di); apply Mx_unit. exists (Nd1 red t'); [ elim eg; trivial | simplify_eq; assumption ].
      intro eg; simpl in |- *; elim eg; trivial.

    (* c = yellow *)
    apply Mx_bind with (1 := core_cop t1).
      intros (t', eg, di); apply Mx_unit. exists (Nd1 yellow t'); [ elim eg; trivial | simplify_eq; assumption ].
      intro eg; simpl in |- *; elim eg; trivial.
Qed.


Theorem eff_cop : forall t : tree1, {t' : tree1 | t' = def_cop t}.
intro t; apply Mx_try with (1 := core_cop t).
    intros (x, e, n); exists x; auto.
    intro eg; exists t; trivial.
Qed.

(* Extracting terms typed in system F but not in ML *)
(* In the extracted ML program, you have to
    - put an Obj.magic in front of each call to mx_try
      (at least for each recursive (then polymorphic) use of mx_try)
*)

Extraction "copy_extr.ml" Mx_unit Mx_raise Mx_try Mx_bind core_cop eff_cop.

