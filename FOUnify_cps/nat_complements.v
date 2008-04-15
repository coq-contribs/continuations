(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(* This contribution was updated for Coq V5.10 by the COQ workgroup.        *)
(* January 1995                                                             *)
(****************************************************************************)
(*                                                                          *)
(*      Coq V5.8                                                            *)
(*                                                                          *)
(*                                                                          *)
(*      First-order Unification                                             *)
(*                                                                          *)
(*      Joseph Rouyer                                                       *)
(*                                                                          *)
(*      November 1992                                                       *)
(*                                                                          *)
(*               New theorems and lemmas on naturals.                       *)
(*                                                                          *)
(****************************************************************************)
(*                            nat_complements.v                             *)
(****************************************************************************)

Require Import Arith.

(*********************************************************************)
(************* Lemmas on naturals proved in Nat.v and *****************)
(******************** used with the command "auto". *******************)
(*********************************************************************)
(*O_S      :(n:nat)(~O=(S n))*)
(*eq_S     :(n:nat)(m:nat)(n=m)->((S n)=(S m))*)
(*eq_add_S :(n:nat)(m:nat)((S n)=(S m))->(n=m)*)
(*le_pred_n:(n:nat)(le (pred n) n)*)
(*le_n_Sn  :(n:nat)(le n (S n))*)
(*le_S_n   :(n:nat)(m:nat)(le (S n) (S m))->(le n m)*)
(*le_Sn_O  :(n:nat)(~(le (S n) O))*)
(*le_n     :(n:nat)(le n n)*)
(*le_n_S   :(n:nat)(m:nat)(le n m)->(le (S n) (S m))*)
(*********************************************************************)

(*********************************************************************)
(********** Logic tools : To translate P:Prop into Q:Set : ****************)
(*********************************************************************)

Definition P_S (A : Set) (P : A -> Prop) (x : A) : Set :=
  {a : A | a = x &  P a}.

Lemma P_S_proof1 : forall (A : Set) (a : A) (P : A -> Prop), P a -> P_S A P a.
intros; unfold P_S in |- *; exists a; auto with v62.
Qed.

Lemma P_S_proof2 : forall (A : Set) (a : A) (P : A -> Prop), P_S A P a -> P a.
unfold P_S in |- *; intros A a P h; elim h; intros x h0; elim h0;
 auto with v62.
Qed.

(*********************************************************************)
(***************** Logic tools  To negate an equality : ******************)
(*********************************************************************)

Lemma Diff :
 forall (A : Set) (f : A -> Prop) (a b : A), f a -> ~ f b -> a <> b.
unfold not in |- *; intros A f a b H H0 H1; elim H0; elim H1; auto with v62.
Qed.

(*** Replace "apply h;auto with v62" by "auto" when the Type of h is False : ***)

Lemma n_False : ~ False.
auto with v62.
Qed.

(*********************************************************************)

(*********************************************************************)
(********************** Section complement_nat. *********************)
(*********************************************************************)

(*Section complement_nat.*)

(*********************************************************************)
(**************** Decidability of the equality in the Set nat : *************)
(*********************************************************************)

Lemma nat_eq_decS : forall x y : nat, {x = y} + {x <> y}.
simple induction x.           
(*case x=O*)
simple induction y; auto with v62.
(*case x=(S y)*)
simple induction y.
(*... case y0=O*)
right; discriminate.
(*... case y0=(S y1)*)
intros y1 h; elim (H y1); intros.
(*... ... case y=y1*)
auto with v62. (*apply eq_S*)
(*case not y=y1*)
right; simplify_eq; auto with v62.
Qed.

Lemma nat_eq_decP : forall x y : nat, x = y \/ x <> y.
intros x y; elim (nat_eq_decS x y); auto with v62.
Qed.

(*********************************************************************)
(************** General induction (with le) : ****************************)
(*********************************************************************)

Lemma ind_leS :
 forall (n : nat) (P : nat -> Set),
 P 0 -> (forall p : nat, (forall q : nat, q <= p -> P q) -> P (S p)) -> P n.
intros n P; cut ((forall m : nat, m <= n -> P m) -> P n).
2: auto with v62. (*apply le_n*)
intros h h0 h1; apply h.
elim n.
(*case n=O*)
(*... case m=O*)
simple induction m.
intros; auto with v62.
(*... case m=(S y)*)    
intros y Hyp1 Hyp2; absurd (S y <= 0); auto with v62. (*le_Sn_O*)
(*case n=(S y)*)
simple induction m.
(*... case m=O*)
auto with v62.
(*... case m=(S y0)*)    
intros y0 hyp1 hyp2; apply (h1 y0).
eauto with v62.
Qed.

Lemma ind_leP :
 forall (n : nat) (P : nat -> Prop),
 P 0 -> (forall p : nat, (forall q : nat, q <= p -> P q) -> P (S p)) -> P n.
intros; apply (P_S_proof2 nat n P).
apply (ind_leS n (P_S nat P));
 [ apply P_S_proof1; assumption | intros; apply P_S_proof1 ].
apply H0; intros; elim (H1 q); [ intros x eg_x_q | auto with v62 ].
rewrite eg_x_q; auto with v62.
Qed.

(*********************************************************************)
(********** Reasoning by cases with the natural constructors : ************)
(*********************************************************************)

Lemma pred_or : forall m : nat, 0 = m \/ m = S (pred m).
intro; elim m; auto with v62.
Qed.

Lemma nat_caseS :
 forall (x : nat) (P : nat -> Set), P 0 -> (forall n : nat, P (S n)) -> P x.
intros; elim x; auto with v62.
Qed.

(*********************************************************************)
(************** Decidability of le : ************************************)
(*********************************************************************)

Lemma le_decS : forall n p : nat, {n <= p} + {~ n <= p}.
simple induction n.
(*case n=O*)
auto with v62.
(*case n=(S y)*)
simple induction p.
auto with v62.           (*apply le_Sn_O*)
intros y0 le_or_not_le; elim (H y0).
auto with v62.             (*apply le_n_S*)
intro not_le_n0_y0; right; unfold not in |- *.
intros; elim not_le_n0_y0; auto with v62.        (*apply le_S_n*)
Qed.

Lemma le_decP : forall n p : nat, n <= p \/ ~ n <= p.
intros; elim (le_decS n p); auto with v62.
Qed.

Lemma le_S_eqS : forall n p : nat, n <= p -> {S n <= p} + {n = p :>nat}.
simple induction n.
simple induction p; auto with v62.
intros n0 H p; elim p.
intros; absurd (S n0 <= 0); auto with v62.
intros n1 H1 H2; elim (H n1); auto with v62. (*le_n_S*)
Qed.

Lemma le_S_eqP : forall n p : nat, n <= p -> S n <= p \/ n = p :>nat.
intros; elim (le_S_eqS n p); auto with v62.
Qed.
