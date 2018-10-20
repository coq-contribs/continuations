(* ============================================================== *)
(*                          applytac.ml                           *)
(* ---                                                            *)
(* Jean-Francois.Monin@lannion.cnet.fr                            *)
(* January 1995, Coq V5.10                                        *)
(* ============================================================== *)

open CErrors
open Term
open EConstr
open Clenv
open Clenvtac
open Tacmach
open Ltac_plugin
open Stdarg

DECLARE PLUGIN "cps/applytac"

let last_constr (sigma,c) = snd (decompose_prod sigma c)

let first_arg sigma =
   let st = "arg of first_arg should be an application"
   in function c -> match kind sigma c with
     App (_, v) -> if Array.length v = 1 then Array.get v 0
                          else user_err (Pp.str (st^" with exactly one argument"))
   | c -> user_err (Pp.str st)

let nb_hyps sigma c = List.length (fst (decompose_prod sigma c))

(* pour un Apply f with typeres_of c *)
let resolve_with_tac chd mlist gls =
  let sigma, ty = pf_type_of gls chd in
  let clause = pf_apply make_clenv_binding_apply gls (Some (nb_hyps sigma ty)) (chd, ty)
    (Misctypes.ImplicitBindings mlist) in
  Proofview.V82.of_tactic (res_pf clause) gls

(* f = com a appliquer; c = com dont on veut le type du resultat *)
let resolve_with_compon translate cpn f c gls =
   let mlist = [cpn gls (translate gls c)]
   in resolve_with_tac (translate gls f) mlist gls

let fst_arg_of_restype gls c = first_arg (project gls) (last_constr (pf_type_of gls c))

(* FATR = first argument of type of result of *)

let applyWithFATR_tac f c =
  resolve_with_compon (fun _ x -> x) fst_arg_of_restype f c

TACTIC EXTEND apply_with_fatr
  [ "apply_with_fatr" constr(f) constr(c) ] -> [ Proofview.V82.tactic (applyWithFATR_tac f c) ]
END
