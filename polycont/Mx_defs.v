(* Contribution to the Coq Library   V6.3 (July 1999)                    *)


Definition Mx (C : Prop) (A : Set) :=
  forall (X : Set) (P : Prop) (e : P -> X), (C -> P) -> (A -> X) -> X.

Definition Mx_unit (C : Prop) (A : Set) (a : A) : Mx C A :=
  fun (X : Set) (P : Prop) (e : P -> X) (i : C -> P) (k : A -> X) => k a.

Definition Mx_raise (C : Prop) (A : Set) (c : C) : 
  Mx C A :=
  fun (X : Set) (P : Prop) (e : P -> X) (i : C -> P) (k : A -> X) => e (i c).

Definition Mx_try (C : Prop) (A : Set) (m : Mx C A) 
  (X : Set) (k : A -> X) (e : C -> X) : X := m X C e (fun p : C => p) k.

Definition Mx_bind (A A' : Set) (C C' : Prop) (m : Mx C A)
  (f : A -> Mx C' A') (j : C -> C') : Mx C' A' :=
  fun (X : Set) (P : Prop) (e : P -> X) (i : C' -> P) (k : A' -> X) =>
  m X P e (fun c : C => i (j c)) (fun a : A => f a X P e i k).