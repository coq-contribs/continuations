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

type 'dom tree =
    Leaf of 'dom
  | Node of 'dom tree * 'dom tree

type 'A list =
    Nil
  | Cons of 'A * 'A list

type direction =
    L
  | R

let lookup a =
  let rec lookup0 = function
    Leaf b ->
      (match (=) a b with
         true -> mx_unit Nil
       | false -> mx_raise prop)
  | Node (t1, t2) -> Obj.magic
      mx_try (lookup0 t1) (fun h -> mx_unit (Cons (L, h))) (fun _ ->
        mx_bind (lookup0 t2) (fun l2 -> mx_unit (Cons (R, l2))) prop)
  in lookup0

let encode a t _ =
  mx_try (lookup a t) (fun x -> x) (fun _ -> Nil)

