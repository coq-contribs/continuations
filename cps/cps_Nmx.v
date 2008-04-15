(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(* Jean-Francois.Monin@lannion.cnet.fr                                      *)
(* October 1994, Coq V5.8.3                                                 *)
(*                                                                          *)
(****************************************************************************)
(*                                 cps_Nmx.v                                *)
(****************************************************************************)

(*
   Txval is the type of exceptions and is supplied by the user. 
   Txval is a dependent type which depends on Txlev, another
   user-defined type representing different levels of exception.

Example :
 
 Inductive Definition Txlev : Set := l1 : Txlev | l2 : Txlev.
 Inductive Definition Txval : Txlev->Set :=
   e1 : (Txval l1) |
   e2 : nat->(Txval l2).
*)

(* 
   The following primitives  should be used in a section
   beginning with 

Load DeclareNmx.

*)

Section defcont.

Variable Txlev : Set.
Variable Txval : Txlev -> Set.

Definition Propxg := forall l : Txlev, Txval l -> Prop.

Variable X : Set.
Variable P : Propxg.
Variable e : forall (l : Txlev) (x : Txval l), P l x -> X.


Definition Nmxglob (C : Propxg) (A : Set) :=
  (forall (l : Txlev) (x : Txval l), C l x -> P l x) -> (A -> X) -> X.

Let Nmx := Nmxglob.

Notation "c \/m+ s" := (Nmx c s)
  (at level 85, right associativity, format "c  \/m+  '/  ' s").

Definition Nmx_unit_glob (C : Propxg) (A : Set) (a : A) : 
  C \/m+ A :=
  fun (i : forall (l : Txlev) (x : Txval l), C l x -> P l x) (k : A -> X) =>
  k a.

Definition Nmx_raise_glob (C : Propxg) (A : Set) (l : Txlev) 
  (x : Txval l) (c : C l x) : C \/m+ A :=
  fun (i : forall (l : Txlev) (x : Txval l), C l x -> P l x) (k : A -> X) =>
  e l x (i l x c).


Definition Nmx_elim_Nmx_glob (A A' : Set) (C C' : Propxg)
  (f : A -> C' \/m+ A')
  (j : forall (l : Txlev) (x : Txval l), C l x -> C' l x) 
  (nx : C \/m+ A) : C' \/m+ A' :=
  fun (i : forall (l : Txlev) (x : Txval l), C' l x -> P l x) (k : A' -> X) =>
  nx (fun (l : Txlev) (x : Txval l) (c : C l x) => i l x (j l x c))
    (fun a : A => f a i k).

Definition Nmx_handle_glob (C : Propxg) (A : Set) (Nmx : C \/m+ A) :
  (forall (l : Txlev) (x : Txval l), C l x -> P l x) -> (A -> X) -> X := Nmx.

End defcont.

