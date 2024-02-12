module R = Raw
module D = Domain

open D

let bind_var (size: int) (k : int -> D.t -> 'a): 'a =
  k (size + 1) (D.Local size)

let rec quote (size : int) (tm : D.t): R.t =
  match tm with
  | Local i -> R.Local (size - i - 1)
  | Lam (a, b) -> R.Lam (a, None, quote_clo size b)
  | Pair (a, b) -> R.Pair (quote size a, quote size b)
  | Pi (nm, a, b) -> R.Pi (nm, quote size a, quote_clo size b)
  | Sigma (nm, a, b) -> R.Sigma (nm, quote size a, quote_clo size b)
  | Univ -> R.Univ

               
and quote_clo (size: int) (clo: D.clo): R.t =
  bind_var size (fun size arg -> quote size @@ Eval.inst_clo clo arg)
