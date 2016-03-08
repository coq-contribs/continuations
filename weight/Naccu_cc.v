(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(* Jean-Francois.Monin@lannion.cnet.fr                                      *)
(* January 1995, Coq V5.10                                                  *)
(*                                                                          *)
(****************************************************************************)
(*                                Naccu_cc.v                                *)
(****************************************************************************)

Require Import tests.
Require Import specif.
Require Import cps_N.

Section algocc.

Load "DeclareN".

Let T_aux (m n : nat) := {n' : nat | n = n' &  ~ m <= n'}.

Ltac Split_condsum c1 c2 c3 := intros s; elim s; clear s; intros c1 c2 c3.

Theorem ex_deb_cc_V1 : forall (m : nat) (t : tree), N (RESU m t).
intros m t.
Ncallcc ipattern:(c).
Napply (condsum_accu m 0 t).
  intro s_cond; elim s_cond; intros n Hnt Hmn.
  Nunit; refine (exres _ _ false _); auto with v62.
  apply Sf; generalize Hmn; rewrite Hnt; auto with v62.

  cut (forall n : nat, (m <= n -> P_overweight_accu m 0 t) -> N (T_aux m n)).
    intro g.

    cut
     (forall a : nat,
      (P_overweight_accu m a t -> P_overweight_accu m 0 t) ->
      N (condsum_accu m a t));
     [ intro comprec; apply comprec; intro Hd; apply Hd | idtac ].
  
  
     pattern t at 1 3 in |- *; elim t.
       intros n a e.
       Napplift (g (a + n));
        [ intro sn;
           refine (let (b, _, _) := sn in condsum_accu_intro _ _ _ b _ _);
           auto with v62
        | auto with v62 ].

      Hint Resolve deb_left_accu_plus deb_right_accu_plus deb_accu_plus_r.
       intros t1 R1 t2 R2 a e.
       Napply (condsum_accu m a t1);
        [ Split_condsum ipattern:(an1) ipattern:(Han1t1) ipattern:(Hman1)
        | apply R1; auto with v62 ].
       Napply (condsum_accu m an1 t2);
        [ Split_condsum ipattern:(an) ipattern:(Hant2) ipattern:(Hmn)
        | apply R2; rewrite Han1t1; auto with v62 ].
       Nunit; refine (condsum_accu_intro _ _ _ an _ _); auto with v62.
       rewrite Hant2; rewrite Han1t1; rewrite plus_assoc_reverse;
        auto with v62.

     (* definition de g *)

     intros n e.
     case (le_dec m n).
       intro le_mn; Nthrow c; Nunit; refine (exres _ _ true _); auto with v62.
          apply St; cut (P_overweight_accu m 0 t); auto with v62.

       intro Nle_mn; Nunit; refine (exist2 _ _ n _ _); auto with v62.
Qed.

End algocc.
(* -------------------- *)


Theorem F_overweight_accu_cc : forall (m : nat) (t : tree), RESU m t.
  intros m t; apply (ex_deb_cc_V1 (RESU m t) m t).
  intro x; exact x.
Qed.

