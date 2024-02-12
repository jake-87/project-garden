module R = Raw
module D = Domain

open R

let rec eval (env: D.env) (e : R.t) : D.t =
  let res = match e with
    | Local ix ->
      D.Local ix
    | Hole -> failwith "todo: holes"
    | Let (_nm, _ty, a, b) ->
       eval (D.extend env (eval env a)) b
    | Lam (a, _ty, b) -> D.Lam(a, {env; tm = b})
    | App (a, b) -> do_app (eval env a) (eval env b)
    | Pi (nm, a, b) ->
      D.Pi (nm, eval env a, {env; tm = b})
    | Pair(a, b) -> D.Pair(eval env a, eval env b)
    | Proj1 i -> do_proj1 (eval env i)
    | Proj2 i -> do_proj2 (eval env i)
    | Sigma (nm, a, b) ->
      D.Sigma (nm, eval env a, {env; tm = b})
    | Univ -> D.Univ
  in
  res
    
and do_app (fn: D.t) (arg: D.t): D.t =
  match fn with
  | D.Lam (_nm, clo) -> inst_clo clo arg
  | _ ->
    failwith "can't app to lam"

and do_proj1 (arg: D.t): D.t =
  match (arg : D.t) with
  | D.Pair (a, _b) -> a
  | _ -> failwith "can't proj1 non-pair"

and do_proj2 (arg: D.t): D.t =
  match arg with
  | D.Pair(_a, b) -> b
  | _ -> failwith "can't proj2 non-pair"
    
and inst_clo clo arg =
  eval (D.extend clo.env arg) clo.tm
  
