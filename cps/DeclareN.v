 (* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                DeclareN.v                                *)
(****************************************************************************)
     Variable X : Set.
     Let N := N_glob X.
     Let N_unit := N_unit_glob X.
     Let NF := NF_glob X.
     Let N_abstr : forall A B : Set, (A -> N B) -> NF A B := N_abstr_glob X.
     Let N_appli : forall A B : Set, NF A B -> N A -> N B := N_appli_glob X.
     Let N_lift : forall A B : Set, (A -> B) -> N A -> N B := N_lift_glob X.
     Let N_letin : forall A B : Set, N A -> NF A B -> N B := N_letin_glob X.
     Let N_seq : forall A B : Set, N A -> N B -> N B := N_seq_glob X.
     Let N_fn : forall (A : Set) (f : A -> A), N A -> N A := N_fn_glob X.
     Let N_op : forall (A : Set) (op : A -> A -> A), N A -> N A -> N A :=
       N_op_glob X.
     Let Tcontcc := Tcontcc_glob X.
     Let contcc := contcc_glob X.
     Let N_callcc : forall A : Set, (Tcontcc A -> N A) -> N A :=
       N_callcc_glob X.
     Let N_throw : forall A B : Set, Tcontcc A -> N A -> N B :=
       N_throw_glob X.



Ltac Nunit := apply N_unit.

Ltac NunitRefine c := apply N_unit; refine c; auto.

Ltac Nabst := apply N_abstr.

Ltac Napply c := apply N_appli with c; [ apply N_abstr | idtac ].

Ltac Nlift c := apply N_lift with c.

Ltac Napplift c := apply_with_fatr N_lift c; [ idtac | apply c ].

Ltac Nletin c := apply N_seq with c.

Ltac Ncallcc c := apply N_callcc; intro c.

Ltac Nthrow c := apply N_throw with (1 := c).