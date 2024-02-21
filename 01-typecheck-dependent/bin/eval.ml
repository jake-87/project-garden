module R = Raw
module D = Domain

open R

let rec eval (env: D.env) (e : R.t) : D.t =
  let res = match e with
    | Local (Ix ix) ->
      D.index env ix
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
  | D.Stuck tm ->
    begin
      D.Stuck (D.App {fn = tm; arg = arg})
    end 
  | _ ->
    print_endline "\noops:";
    D.print fn;
    D.print arg;
    failwith "can't apply to non-lambda"


and do_proj1 (arg: D.t): D.t =
  match (arg : D.t) with
  | D.Pair (a, _b) -> a
  | D.Stuck tm ->
    D.Stuck (D.Fst tm)
  | _ ->
    failwith "proj1"

    
and do_proj2 (arg: D.t): D.t =
  match arg with
  | D.Pair(_a, b) -> b
  | D.Stuck tm ->
    D.Stuck (D.Snd tm)
  | _ ->
    failwith "proj2"
    
and inst_clo clo arg =
  eval (D.extend clo.env arg) clo.tm
  
