(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(* Jean-Francois.Monin@lannion.cnet.fr                                      *)
(* January 1995, Coq V5.10                                                  *)
(*                                                                          *)
(****************************************************************************)
(*                                  cps_N.v                                 *)
(****************************************************************************)

(* ================================================== *)
(*      Continuation Passing Style translation        *)
(* ================================================== *)


Section defcont.

Variable X : Set.

Definition N_glob (A : Set) := (A -> X) -> X.

Let N := N_glob.

Definition N_unit_glob (A : Set) (a : A) : N A := fun k : A -> X => k a.


(* For application *)
Definition NF_glob (A B : Set) := N (A -> N B).

Let NF := NF_glob.

Definition N_abstr_glob (A B : Set) (M : A -> N B) : 
  NF A B := fun k : (A -> N B) -> X => k (fun x : A => M x).

(* equivalent definition 
Definition N_abstr_glob (A,B:Set) : (A->(N B)) ->(NF A B) :=
    fun M: (A->(N B)) -> (N_unit_glob A->(N B) M).
*)


Definition N_appli_glob (A B : Set) (f_c : NF A B) 
  (a_c : N A) : N B :=
  fun k : B -> X => f_c (fun f : A -> N B => a_c (fun a : A => f a k)).

Definition N_lift_glob (A B : Set) (f : A -> B) (a_c : N A) : 
  N B := fun k : B -> X => a_c (fun a : A => k (f a)).


Definition N_letin_glob (A B : Set) (a_c : N A) (f_c : NF A B) : 
  N B := fun k : B -> X => a_c (fun a : A => f_c (fun f : A -> N B => f a k)).


(* a;b  <==> let x=a in b  *)

Theorem N_seq_glob : forall A B : Set, N A -> N B -> N B.
  intros A B a_c b_c.
  apply N_letin_glob with (1 := a_c).
  apply N_abstr_glob; intro x; exact b_c.
Defined.

    
(* -------------------- *)

Definition N_fn_glob (A : Set) (f : A -> A) (x_c : N A) : 
  N A := fun k : A -> X => x_c (fun x : A => k (f x)).

Definition N_op_glob (A : Set) (op : A -> A -> A) (x_c y_c : N A) : 
  N A := fun k : A -> X => x_c (fun x : A => y_c (fun y : A => k (op x y))).



(* ============================== *)

(* ---------------------------------------- *)
(*             Control Operators            *)
(* ---------------------------------------- *)


(* continuation catched for escapement *)
Definition Tcontcc_glob (A : Set) := A -> forall B : Set, N B.
Let Tcontcc := Tcontcc_glob.

Definition contcc_glob (A : Set) (k : A -> X) : Tcontcc A :=
  fun (a : A) (B : Set) (k' : B -> X) => k a.

Definition N_callcc_glob (A : Set) (cour : Tcontcc A -> N A) : 
  N A :=
  fun k : A -> X => cour (fun (a : A) (B : Set) (k' : B -> X) => k a) k.


Definition N_throw_glob (A B : Set) : Tcontcc_glob A -> N A -> N B :=
  fun (c : Tcontcc A) (a_c : N A) (k' : B -> X) =>
  a_c (fun a : A => c a B k').


End defcont.

Require Export applytac.
