(* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                                                          *)
(* Jean-Francois.Monin@lannion.cnet.fr                                      *)
(* August 1994, Coq V5.8.3                                                  *)
(*                                                                          *)
(****************************************************************************)
(*                               Nmxaccu_ex.v                               *)
(****************************************************************************)

(* Version with 2 exceptions *)

Require Import tests.
Require Import specif.

Require Import cps_Nmx.

Require Import decl_exc.

Section algo1.

Load "DeclareNmx".

Theorem prop_exc : forall Pz Pd : Prop, Propx.
  unfold Propx, Propxg in |- *; intros Pz Pd l.
  case l.
    intro zer; exact Pz.

    intro b; exact ((b = xv2 true -> Pd) /\ (b = xv2 false -> False)).
Defined.


Definition condsum2_accu_cps (m a : nat) (t : tree) :=
  prop_exc (Pposs_zer t) (P_overweight_accu m a t) Vm+ condsum_accu m a t.

Definition condsum2_accu_handle (m : nat) (t : tree)
  (nx : condsum2_accu_cps m 0 t) :
  (forall (l : Txlev) (x : Txval l),
   prop_exc (Pposs_zer t) (P_overweight_accu m 0 t) l x -> P l x) ->
  (condsum_accu m 0 t -> X) -> X :=
  Nmx_handle (prop_exc (Pposs_zer t) (P_overweight_accu m 0 t))
    (condsum_accu m 0 t) nx.

Definition T_aux (m n : nat) := {n' : nat | n = n' &  ~ m <= n'}.

Ltac Split_condsum c1 c2 c3 := let s := fresh "s" in intro s; elim s; clear s; intros c1 c2 c3.
Theorem core_V2 : forall (m : nat) (t : tree), condsum2_accu_cps m 0 t.

do 2 intro.
cut (forall n : nat, prop_exc False (m <= n) Vm+ T_aux m n).
   intro g.
   cut (forall a : nat, condsum2_accu_cps m a t);
    [ intro comprec; apply comprec | idtac ].
   unfold condsum2_accu_cps in |- *; elim t.
     intros n a.
     case (nul_dec n).
       intro H0; NmxRaise xv1; simpl in |- *; elim H0; auto with v62.
       unfold not in |- *; intro Hn0; NmxElim (g (a + n));
        [ intro sn'; NmxUnit;
           refine (let (n', _, _) := sn' in condsum_accu_intro _ _ _ n' _ _);
           auto with v62
        | AutoTx ].
  
     Hint Resolve deb_left_accu_plus deb_right_accu_plus deb_accu_plus_r.
     intros t1 R1 t2 R2 a.
     NmxElim (R1 a);
      [ Split_condsum ipattern:(an1) ipattern:(Han1t1) ipattern:(Hman1) | AutoTx ]. 
     NmxElim (R2 an1);
      [ Split_condsum ipattern:(an) ipattern:(Hant2) ipattern:(Hmn)
      | rewrite Han1t1; AutoTx ]. 
     NmxUnit; refine (condsum_accu_intro _ _ _ an _ _); auto with v62.
     rewrite Hant2; rewrite Han1t1; rewrite plus_assoc_reverse; simpl in |- *;
      auto with v62.

     (* definition de g *)

   intro n; case (le_dec m n).
     Hint Resolve noteq_xv2_true_false. 
     intro Hlemn; NmxRaise (xv2 true); simpl in |- *; auto with v62.
     intro Nlemn; NmxUnit; refine (exist2 _ _ n _ _); auto with v62.
Qed.

End algo1.

Theorem success2 :
 forall (m : nat) (t : tree), condsum_accu m 0 t -> RESU2 m t.
  intros m t ca; exists (some_b false).
  elim ca; simpl in |- *.
  intros n Hn; rewrite Hn; auto with v62.
Qed.

(* ==> [_:nat] ([_:tree] ([_:nat] (some_b false))) *)


Theorem exc_overweight_accu :
 forall (m : nat) (t : tree) (l : Txlev) (x : Txval l),
 prop_exc (Pposs_zer t) (P_overweight_accu m 0 t) l x -> RESU2 m t.

intros m t l; case l. 
  intros x1 Hexc1; exists exc_b; auto with v62.

  intros x2 Hexc2; exists (some_b (xl2_bool x2)).
  generalize Hexc2; clear Hexc2; rewrite (inv_xv2_xl2_bool x2).
  elim (xl2_bool x2); simpl in |- *; intro Hexc2; elim Hexc2; intros Ht Hf.
    cut (m <= 0 + leaveplus t);
     [ auto with v62 | elim Ht; simpl in |- *; auto with v62 ].

    elim Hf; auto with v62.
Qed.

(* ==> [_:nat]([_:tree]([l:Txlev]
           <Txval->boolexc>Case l of
                  ([_:Txval] exc_b)
                  ([x2:Txval](some_b (xl2_bool x2)))
                  end))
*)


Theorem F_overweight_V2 : forall (m : nat) (t : tree), RESU2 m t.
intros m t;
 apply
  condsum2_accu_handle
   with (prop_exc (Pposs_zer t) (P_overweight_accu m 0 t)) m t.
   apply core_V2; exact (exc_overweight_accu m t).
   intros l x h; exact h.
   exact (success2 m t).
Qed.

(* ==> [m:nat][t:tree]
         (condsum2_accu_handle boolexc m t
             (core_V2 boolexc (exc_overweight_accu m t) m t) (success2 m t))
*)


Section algo2.

Load "DeclareNmx".

Theorem prop_excl : forall Pz : Prop, Propx.
  unfold Propx, Propxg in |- *; intros Pz l.
  elim l.
    intro zer; exact Pz.

    intro b; exact False.
Defined.

Definition lcond_cps (m : nat) (lt : ltree) :=
  prop_excl (Pposs_zerl lt) Vm+ lcond m lt.

Definition lcond_handle (m : nat) (lt : ltree) (nx : lcond_cps m lt) :
  (forall (l : Txlev) (x : Txval l), prop_excl (Pposs_zerl lt) l x -> P l x) ->
  (lcond m lt -> X) -> X :=
  Nmx_handle (prop_excl (Pposs_zerl lt)) (lcond m lt) nx.

Definition SPEC_resu_aux (m : nat) (t : tree) (b : bool) :=
  (b = true -> P_overweight_accu m 0 t) /\
  (b = false -> ~ P_overweight_accu m 0 t).

Definition Tl_aux (m : nat) (t : tree) :=
  {b : bool | SPEC_resu_aux m t b (* & ~(Pposs_zer t) *)}.
(*                                                 ^^^^^^^^^^^^^^^^
   We cannot guarantee that t has no zero, because another exception
   (overweight) could have been raised before the discovery of a zero.
*)

Theorem catch_overweight :
 forall (m : nat) (t : tree) (l : Txlev) (x : Txval l),
 prop_exc (Pposs_zer t) (P_overweight_accu m 0 t) l x ->
 prop_excl (Pposs_zer t) Vm+ Tl_aux m t.

intros m t l; case l; simpl in |- *; intros v Hv.
   NmxRaise xv1; simpl in |- *; auto with v62.

   NmxUnit; refine (exist _ (xl2_bool v) _); auto with v62.
   unfold SPEC_resu_aux in |- *; elim Hv; intros Ht Hf; split.
      intro Hxt; apply Ht; elim Hxt; apply inv_xv2_xl2_bool.
      intro Hxf; elim Hf; elim Hxf; apply inv_xv2_xl2_bool.
Qed.

(* ==> [_:nat]([_:tree]([l:Txlev]
          <Txval->(Nmx Tl_aux)>Case l of
             ([_:Txval] (Nmx_raise X e xl1 xv1 Tl_aux))
             ([v:Txval] (Nmx_unit X Tl_aux (xl2_bool v)))
             end))
*)

Theorem core_list : forall (m : nat) (lt : ltree), lcond_cps m lt.
do 2 intro; unfold lcond_cps in |- *.
elim lt.
  NmxUnit. refine (clc _ _ nilb _); auto with v62.

  clear lt; intros t lt Rlt.
  cut (prop_excl (Pposs_zer t) Vm+ Tl_aux m t).
    intro g.
    NmxElim g; [ intro aux_b | AutoTx ].
      NmxElim Rlt;
       [ intro Rlb; NmxUnit;
          refine
           (let (b, s) := aux_b in
            let (lb, s') := Rlb in clc _ _ (consb b lb) _); 
          auto with v62
       | AutoTx ].
         elim s; inversion s'; elim b; unfold P_overweight_accu in |- *;
          auto with v62.

   (* Definition of g *)

      apply
       condsum2_accu_handle
        with (prop_exc (Pposs_zer t) (P_overweight_accu m 0 t)) m t.
      apply core_V2; exact (catch_overweight m t).

      intros l x; intro h; exact h.
    
      intro s; elim s; simpl in |- *; intros n Hnt Hmn.
      NmxUnit. refine (exist _ false _); auto with v62.
      unfold SPEC_resu_aux in |- *; split.
         intro E; discriminate E.
 
         intro triv; unfold not in |- *; intro Hov.
         apply Hmn; rewrite Hnt; elim Hov; auto with v62.
Qed.      

End algo2.

Theorem excl_overweight_list :
 forall (m : nat) (lt : ltree) (l : Txlev) (x : Txval l),
 prop_excl (Pposs_zerl lt) l x -> RESUL m lt.
intros m lt l x Hexc; exists exc_lb.
generalize l x Hexc; clear Hexc x l; AutoTx.
Qed.

(* ==> [_:nat] ([_:ltree] ([_:Txlev] ([_:Txval] exc_lb))) *)


Theorem success_list :
 forall (m : nat) (lt : ltree), lcond m lt -> RESUL m lt.
intros m lt lc; case lc; intros lb Hlb.
exists (some_lb lb); auto with v62.
Qed.

(* ==> [_:nat] ([_:ltree] ([lc:lbool](some_lb lc))) *)


Theorem F_overweight_list : forall (m : nat) (lt : ltree), RESUL m lt.
intros m lt.
apply lcond_handle with (prop_excl (Pposs_zerl lt)) m lt.
   apply core_list; exact (excl_overweight_list m lt).
   intros l x h; exact h.
   exact (success_list m lt).
Qed.

(* ==> [m:nat][lt:ltree]
          (lcond_handle lboolexc m lt
             (core_list lboolexc (excl_overweight_list m lt) m lt)
             (success_list m lt))
*)

(* :======================================================= *)