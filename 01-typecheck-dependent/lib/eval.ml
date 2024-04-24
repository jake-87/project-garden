module S = Syntax
module D = Domain
module H = Helpers
module M = Metas
open D.Constructors

(* eval syntax to domain
   general structure is to try and simplify stuff as much as possible
   apply simplifications like beta as much as possible
   currently:
   (λx. f) a -> f[x := a]
   (a, b) .fst -> a
   (a, b) .snd -> b
   otherwise, add them to the pile of eliminators on something
   term .fst .snd .ap(b)
   <=>
   (snd (fst term)) b

   for anything that takes an argument (lambda, pi, sg)
   we stick it in a closure
   
*)


let rec eval (env: D.env) (tm: S.syn): D.dom =
  match tm with
  | S.Local ix ->
    let (_, dom) = D.index env ix in dom
  | S.Let (_nm, _typ, head, body) -> eval (D.add env Defined (eval env head)) body
  | S.Lam (nm, t) -> D.Lam (nm, D.{tm = t; env})
  | S.Ap (a, b) ->
    let a' = eval env a in
    let b' = eval env b in
    (match a' with
     | D.Lam (_nm, bd) -> inst_clo bd D.Bound b'
     | D.Stuck s -> D.Stuck (D.add_elim s (D.Ap b'))
     | _ -> H.cannot "impossible"
    )
  | S.Pair (a, b) -> pair (eval env a) (eval env b)
  | S.First f ->
    let f' = eval env f in
    (match f' with
     | D.Pair (a, _) -> a
     | D.Stuck s -> D.Stuck (D.add_elim s (D.First))
     | _ -> H.cannot "impossible"
    )
  | S.Second f ->
    let f' = eval env f in
    (match f' with
     | D.Pair (_, b) -> b
     | D.Stuck s -> D.Stuck (D.add_elim s (D.Second))
     | _ -> H.cannot "impossible"
    )
  | S.Pi (nm, a, b) ->  pi nm (eval env a) (clo b env)
  | S.Sg (nm, a, b) -> sg nm (eval env a) (clo b env)
  | S.Meta m -> D.Stuck (app_bds env D.{tm = D.Meta m; elims = []})
  | S.Univ -> D.Univ

and app_bds (env: D.env) (m: D.stuck): D.stuck =
  match env with
  | [] -> m
  | (Bound, d) :: xs -> D.add_elim (app_bds xs m) (D.Ap d)
  | (Defined, _d) :: xs -> app_bds xs m

and inst_clo (clo: D.clo) (bd: D.bd) (new': D.dom) = eval (D.add clo.env bd new') clo.tm
