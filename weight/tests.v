(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(* Jean-Francois.Monin@lannion.cnet.fr                                      *)
(* December 1994, Coq V5.10                                                 *)
(*                                                                          *)
(****************************************************************************)
(*                                  tests.v                                 *)
(****************************************************************************)

(* Comparison of 2 natural numbers *)

Require Export Le.

Theorem le_dec : forall m n : nat, {m <= n} + {~ m <= n}.
simple induction m; clear m.
  intro n; left; auto with arith.
  intros m bm n; elim n; clear n.
    right; auto with arith.
    intros n bSmn; clear bSmn. 
    elim bm with n. 
      intro le_mn; left; auto with arith.
      intro Nle_mn; right; unfold not in |- *; auto with arith.
Qed.


(* Test to zero *)

Theorem nul_dec : forall n : nat, {0 = n :>nat} + {0 <> n :>nat}.
simple destruct n; auto with arith.
Qed.

(* =========================== *)

