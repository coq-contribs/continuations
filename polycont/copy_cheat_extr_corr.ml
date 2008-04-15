type nat =
    O
  | S of nat


(* type 'a mx = unit -> x -> ('a -> x) -> x *)

let mx_unit a0 e k =
  k a0


let mx_raise e k =
  e


let mx_try m k e =
  m e k


let mx_bind m f e k =
  m e (fun a0 -> f a0 e k)


type color =
    Blue
  | Red
  | Yellow


type tree1 =
    Leaf of nat
  | Nd1 of color * tree1


let core_cop t =
  let rec f1 = function
    Leaf n -> mx_raise
  | Nd1 (c, t1) ->
      (match c with
         Blue ->
           mx_unit
             (mx_try (f1 t1) (fun h -> Nd1 (Red, h)) (Nd1 (Red, t1)))
       | Red -> mx_bind (f1 t1) (fun h -> mx_unit (Nd1 (Red, h)))
       | Yellow -> mx_bind (f1 t1) (fun h -> mx_unit (Nd1 (Yellow, h))))
  in f1 t


let eff_cop t =
  mx_try (core_cop t) (fun x -> x) t


