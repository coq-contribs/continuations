(* Contribution to the Coq Library   V6.3 (July 1999)                    *)
(*
  The following is an algorithm for extracting the path leading to an item v
  in a binary tree. This path is the code of the item in huffman compression.
  The algorithm is used only when the given item is is the tree.

    exception Not_found
    let encode t v = 
       let rec lookup = function
              Leaf -> raise Not_found
            | Node(t1,b,t2) -> 
                 if a=b then []
                 else try L::lookup t1 with
                      Not_found -> R::lookup t2 
       in lookup t

  The informal argument is as follows : if the item has not been found in the
  left branch (the raised exception is catched), then if the item has not
  been found in the right branch, then nothing has to be done : the raised
  exception will propagate, which means that the item was not in the current
  subtree.

  It is not necessary to be aware of this reasoning when building the formal
  proof: the right proof obligations are automatically generated and are easy
  to prove.

*)

Require Import List.
Require Extraction.

Section sec_dom.
Variable dom : Set.
Variable a : dom.
Axiom eg : forall a b : dom, {a = b} + {a <> b}.

Inductive tree : Set :=
  | Leaf : tree
  | Node : tree -> dom -> tree -> tree.

Inductive direction : Set :=
  | L : direction
  | R : direction. 

Definition ld := list direction.

Fixpoint elsewhere (t : tree) : Prop :=
  match t with
  | Leaf => True
  | Node t1 b t2 => elsewhere t1 /\ a <> b /\ elsewhere t2
  end.

Inductive path : ld -> tree -> Prop :=
  | path_leaf : forall t1 t2 : tree, path nil (Node t1 a t2)
  | path_node1 :
      forall (t1 t2 : tree) (b : dom) (l : ld),
      path l t1 -> path (L :: l) (Node t1 b t2)
  | path_node2 :
      forall (t1 t2 : tree) (b : dom) (l : ld),
      path l t2 -> path (R :: l) (Node t1 b t2).
Hint Resolve path_leaf path_node1 path_node2: huffman.

Lemma not_elsewhere :
 forall (t : tree) (l : ld), path l t -> elsewhere t -> False.
intros t l p. elim p; clear p l; simpl in |- *; try tauto.
(*  Intros t1 t2 (e1,(N,e2)); Case N; Reflexivity. *)
Qed.

Require Import Mx_defs.

Theorem lookup : forall t : tree, Mx (elsewhere t) {l : ld | path l t}.
fix 1.
intro t; case t; clear t.
  apply Mx_raise. simpl in |- *; trivial.
  intros t1 b t2; case (eg a b).
    intro E; apply Mx_unit. exists (nil (A:=direction)); case E; auto with huffman.

    intro N; apply Mx_try with (1 := lookup t1).
    intros (l, Hl). apply Mx_unit. exists (L :: l); auto with huffman.
    intro elsewhere_t1. apply Mx_bind with (1 := lookup t2).
      intros l2; apply Mx_unit; case l2; intros l Hl; exists (R :: l);
       auto with huffman.
      intro elsewhere_t2; simpl in |- *; auto. 
Defined.

Theorem encode :
 forall t : tree, (exists l : ld, path l t) -> {l : ld | path l t}.
intros t Ht.
apply Mx_try with (1 := lookup t).
  intro x; exact x.
  intro et; exists (nil (A:=direction)). 
    case Ht; intros l p. case (not_elsewhere t l); assumption. 
Defined.

End sec_dom.

(* Extracting terms typed in system F but not in ML *)
(* In the extracted ML program, you have to
    - put an Obj.magic in front of each call to mx_try
      (at least for each recursive (then polymorphic) use of mx_try)
*)

Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Constant eg => "(=)".

Extraction "huff_extr.ml" Mx_unit Mx_raise Mx_try Mx_bind lookup encode.
Extraction Inline Mx_bind Mx_unit Mx_raise Mx_try.
Extraction "huff_opt_extr.ml" lookup encode.
