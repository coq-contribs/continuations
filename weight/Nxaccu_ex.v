(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(* Jean-Francois.Monin@lannion.cnet.fr                                      *)
(* December 1994, Coq V5.10                                                 *)
(*                                                                          *)
(****************************************************************************)
(*                                Nxaccu_ex.v                               *)
(****************************************************************************)

(* Using Nx: only one exception *)

Require Import tests.
Require Import specif.
Require Import cps_Nx.

Section algorithms.

Load "DeclareNx".

Definition condsum_accu_cps (m a : nat) (t : tree) :=
  P_overweight_accu m a t \/+ condsum_accu m a t.

Definition condsum_accu_handle (m : nat) (t : tree)
  (nx : condsum_accu_cps m 0 t) :
  (P_overweight_accu m 0 t -> P) -> (condsum_accu m 0 t -> X) -> X :=
  Nx_handle (P_overweight_accu m 0 t) (condsum_accu m 0 t) nx.

Let T_aux (m n : nat) := {n' : nat | n = n' &  ~ m <= n'}.

Ltac Split_condsum c1 c2 c3 := let s := fresh "s" in intro s; elim s; clear s; intros c1 c2 c3.

Theorem core_V1 : forall (m : nat) (t : tree), condsum_accu_cps m 0 t.
do 2 intro.
cut (forall n : nat, m <= n \/+ T_aux m n).
   intro g.
   cut (forall a : nat, condsum_accu_cps m a t);
    [ intro comprec; apply comprec | idtac ].
   unfold condsum_accu_cps in |- *; elim t.
     intros n a.
     NxElim (g (a + n)); [ intro sn' | auto with v62 ].
     NxUnit;
      refine (let (n', _, _) := sn' in condsum_accu_intro _ _ _ n' _ _);
      auto with v62.
     Hint Resolve deb_left_accu_plus deb_right_accu_plus deb_accu_plus_r.
     intros t1 R1 t2 R2 a.
     NxElim (R1 a);
      [ Split_condsum ipattern:(an1) ipattern:(Han1t1) ipattern:(Hman1)
      | auto with v62 ].
     NxElim (R2 an1);
      [ Split_condsum ipattern:(an) ipattern:(Hant2) ipattern:(Hmn)
      | rewrite Han1t1; auto with v62 ].
     NxUnit; refine (condsum_accu_intro _ _ _ an _ _); auto with v62.
     rewrite Hant2; rewrite Han1t1; rewrite plus_assoc_reverse; simpl in |- *;
      auto with v62.

     (* definition of g *)

   intro n; case (le_dec m n).
     intro Hlemn; NxRaise; assumption.
     intro Nlemn; NxUnit; refine (exist2 _ _ n _ _); auto with v62.
Qed.

End algorithms.

Theorem exc_overweight_accu :
 forall (m : nat) (t : tree), P_overweight_accu m 0 t -> RESU m t.
intros; exists true; auto with v62.
Qed.


Theorem success : forall (m : nat) (t : tree), condsum_accu m 0 t -> RESU m t.
intros m t Hsc.
exists false.
elim Hsc; simpl in |- *.
intros n Hn; rewrite Hn; auto with v62.
Qed.

(* ==> [m:nat][t:tree][Hsc:condsum](exres m t false) *)


Theorem F_overweight_accu_V1 : forall (m : nat) (t : tree), RESU m t.
intros m t; apply condsum_accu_handle with (P_overweight_accu m 0 t) m t.
   apply core_V1; exact (exc_overweight_accu m t).
   intro h; exact h. 
   exact (success m t).
Qed.

(* ======================================================= *)

