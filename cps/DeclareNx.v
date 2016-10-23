 (* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                                DeclareNx.v                               *)
(****************************************************************************)

     Variable X : Set.
     Variable P : Prop.
     Variable e : P -> X.
     Let Nx := Nxglob X P.
     Notation Local "c \/+ s" := (Nx c s)
       (at level 85, right associativity, format "c  \/+  '/  ' s").
     Let Nx_handle := Nx_handle_glob X P.
     Let Nx_unit := Nx_unit_glob X P.
     Let Nx_raise := Nx_raise_glob X P e.
     Let Nx_elim_Nx :
       forall (A A' : Set) (C C' : Prop),
       (A -> C' \/+ A') -> (C -> C') -> C \/+ A -> C' \/+ A' :=
       Nx_elim_Nx_glob X P.

Ltac NxUnit := apply Nx_unit.

Ltac NxUnitRefine c := apply Nx_unit; refine c; auto.

Ltac NxRaise := apply Nx_raise.

Ltac NxElim c := apply Nx_elim_Nx with (3 := c).