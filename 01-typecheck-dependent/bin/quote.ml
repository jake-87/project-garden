module R = Raw
module D = Domain

open D

let rec quote (size : int) (tm : D.t): R.t =
  match tm with
  | Stuck s -> quote_stuck size s
  | Lam (a, b) -> R.Lam (a, None, quote_clo size b)
  | Pair (a, b) -> R.Pair (quote size a, quote size b)
  | Pi (nm, a, b) -> R.Pi (nm, quote size a, quote_clo size b)
  | Sigma (nm, a, b) -> R.Sigma (nm, quote size a, quote_clo size b)
  | Univ -> R.Univ

and quote_stuck size (s: stuck): R.t =
  match s with
  | D.App {fn; arg} ->
    let quot = quote_stuck size fn in
    App(quot, quote size arg)
  | D.Fst s ->
    let quot = quote_stuck size s in
    R.Proj1 quot
  | D.Snd s ->
    let quot = quote_stuck size s in
    R.Proj2 quot
  | D.Var (Lvl i) ->
    R.Local (Ix (Debru.lvl_to_ix size i))
    

and quote_clo (size: int) (clo: D.clo): R.t =
  quote (size + 1) @@ Eval.inst_clo clo (D.Stuck (D.Var (Lvl size)))

