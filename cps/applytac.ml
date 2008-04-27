(* ============================================================== *)
(*                          applytac.ml                           *)
(* ---                                                            *)
(* Jean-Francois.Monin@lannion.cnet.fr                            *)
(* January 1995, Coq V5.10                                        *)
(* ============================================================== *)

open Util
open Term
open Proof_type
open Clenv
open Clenvtac
open Tacmach

let last_constr c = snd (decompose_prod c)

let first_arg =
   let st = "arg of first_arg should be an application"
   in function c -> match kind_of_term c with
     App (_, v) -> if Array.length v = 1 then Array.get v 0 
                          else error (st^" with exactly one argument")
   | c -> error st

let nb_hyps c = List.length (fst (decompose_prod c))

(* pour un Apply f with typeres_of c *)
let resolve_with_tac chd mlist gls =
  let ty = pf_type_of gls chd in
  let clause = make_clenv_binding_apply true (Some (nb_hyps ty)) gls (chd, ty)
    (Rawterm.ImplicitBindings mlist) in
  res_pf clause gls

(* f = com a appliquer; c = com dont on veut le type du resultat *)
let resolve_with_compon translate cpn f c gls =
   let mlist = [Evd.empty,cpn gls (translate gls c)]
   in resolve_with_tac (translate gls f) mlist gls

let fst_arg_of_restype gls c = first_arg(last_constr (pf_type_of gls c))
      
(* FATR = first argument of type of result of *)

let applyWithFATR_tac f c =
  resolve_with_compon (fun _ x -> x) fst_arg_of_restype f c

TACTIC EXTEND apply_with_fatr
  [ "apply_with_fatr" constr(f) constr(c) ] -> [ applyWithFATR_tac f c ] 
END
