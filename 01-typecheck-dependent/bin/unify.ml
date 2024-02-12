module D = Domain
module R = Raw
module Q = Quote
module E = Eval

let rec unify (lvl: int) (t1: D.t) (t2: D.t): bool =
  match (t1, t2) with
  | Local i, Local j -> i = j
  | Lam (_, c1), Lam (_, c2) ->
    unify (lvl + 1)
      (E.inst_clo c1 (Local lvl))  
      (E.inst_clo c2 (Local lvl))
  | Pair (a1, b1), Pair (a2, b2) ->
    unify lvl a1 b1 && unify lvl a2 b2
  | Sigma (_, t1, c1), Sigma(_, t2, c2)
  | Pi (_, t1, c1), Pi(_, t2, c2) ->
    unify lvl t1 t2
    && unify (lvl + 1)
      (E.inst_clo c1 (Local lvl))
      (E.inst_clo c2 (Local lvl))
  | Univ, Univ -> true
  | _, _ -> false
