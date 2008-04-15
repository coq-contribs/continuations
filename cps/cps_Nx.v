(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(* Jean-Francois.Monin@lannion.cnet.fr                                      *)
(* December 1994, Coq V5.10                                                 *)
(*                                                                          *)
(****************************************************************************)
(*                                 cps_Nx.v                                 *)
(****************************************************************************)

(* 
   The following primitives  should be used in a section
   beginning with 

Load DeclareNx.

*)

Section defcont.

Variable X : Set.
Variable P : Prop.
Variable e : P -> X.


Definition Nxglob (C : Prop) (A : Set) := (C -> P) -> (A -> X) -> X.

Let Nx := Nxglob.

Notation "c \/+ s" := (Nx c s)
  (at level 85, right associativity, format "c  \/+  '/  ' s").

Definition Nx_unit_glob (C : Prop) (A : Set) (a : A) : 
  C \/+ A := fun (i : C -> P) (k : A -> X) => k a.

Definition Nx_raise_glob (C : Prop) (A : Set) (c : C) : 
  C \/+ A := fun (i : C -> P) (k : A -> X) => e (i c).


Definition Nx_elim_Nx_glob (A A' : Set) (C C' : Prop) 
  (f : A -> C' \/+ A') (j : C -> C') (nx : C \/+ A) : 
  C' \/+ A' :=
  fun (i : C' -> P) (k : A' -> X) =>
  nx (fun c : C => i (j c)) (fun a : A => f a i k).


Definition Nx_handle_glob (C : Prop) (A : Set) (nx : C \/+ A) :
  (C -> P) -> (A -> X) -> X := nx.

End defcont.

