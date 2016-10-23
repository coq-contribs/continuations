 (* Contribution to the Coq Library   V6.3 (July 1999)                    *)

(****************************************************************************)
(*                               DeclareNmx.v                               *)
(****************************************************************************)
     Variable X : Set.
     Let Propx := Propxg Txlev Txval.
     Variable P : Propx.
     Variable e : forall (l : Txlev) (x : Txval l), P l x -> X.
     Let Nmx := Nmxglob Txlev Txval X P.
     Notation "c 'Vm' + s" := (Nmx c s)
       (at level 90, right associativity, s at level 70,
        format "c  'Vm' +  '/  ' s").
     Let Nmx_handle := Nmx_handle_glob Txlev Txval X P.
     Let Nmx_unit := Nmx_unit_glob Txlev Txval X P.
     Let Nmx_raise := Nmx_raise_glob Txlev Txval X P e.
     Let Nmx_elim_Nmx :
       forall (A A' : Set) (C C' : Propx),
       (A -> C' Vm+ A') ->
       (forall (l : Txlev) (x : Txval l), C l x -> C' l x) ->
       (C Vm+ A) -> C' Vm+ A' := Nmx_elim_Nmx_glob Txlev Txval X P.

Ltac NmxUnitRefine c := apply Nmx_unit; refine c; auto.

Ltac NmxUnit := apply Nmx_unit.

Ltac NmxRaise c := apply Nmx_raise with (x := c).

Ltac NmxElim c := apply Nmx_elim_Nmx with (3 := c).