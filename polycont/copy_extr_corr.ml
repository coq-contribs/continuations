type prop = unit
let prop = ()

type arity = unit
let arity = ()

let mx_unit a e _ k =
  k a

let mx_raise _ e _ k =
  e prop

let mx_try m k e =
  m e prop k

let mx_bind m f _ e _ k =
  m e prop (fun a -> f a e prop k)

type nat =
    O
  | S of nat

type color =
    Blue
  | Red
  | Yellow

type tree1 =
    Leaf of nat
  | Nd1 of color * tree1

let core_cop x =
  let rec core_cop0 = function
    Leaf n -> mx_raise prop
  | Nd1 (c, t1) ->
      (match c with
         Blue -> Obj.magic
           mx_try (core_cop0 t1) (fun h -> mx_unit (Nd1 (Red, h)))
             (fun _ -> mx_unit (Nd1 (Red, t1)))
       | Red ->
           mx_bind (core_cop0 t1) (fun h -> mx_unit (Nd1 (Red, h)))
             prop
       | Yellow ->
           mx_bind (core_cop0 t1) (fun h -> mx_unit (Nd1 (Yellow, h)))
             prop)
  in core_cop0 x

let eff_cop t =
  mx_try (core_cop t) (fun h -> h) (fun _ -> t)

