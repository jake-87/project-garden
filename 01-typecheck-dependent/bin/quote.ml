module R = Raw
module D = Domain

open D

let rec quote (size : int) (tm : D.t): R.t =
  match tm with
  | Local ((Lvl i), t) ->
    let loc = R.Local (Ix (Debru.lvl_to_ix size i)) in
    quote_app size loc t
  | Lam (a, b) -> R.Lam (a, None, quote_clo size b)
  | Pair (a, b) -> R.Pair (quote size a, quote size b)
  | Pi (nm, a, b) -> R.Pi (nm, quote size a, quote_clo size b)
  | Sigma (nm, a, b) -> R.Sigma (nm, quote size a, quote_clo size b)
  | Univ -> R.Univ

and quote_app size loc t =
  match t with
  | [] -> loc
  | u :: sp -> App ((quote_app size loc sp), (quote size u))

and quote_clo (size: int) (clo: D.clo): R.t =
  quote (size + 1) @@ Eval.inst_clo clo (D.Local ((Lvl size), []))

