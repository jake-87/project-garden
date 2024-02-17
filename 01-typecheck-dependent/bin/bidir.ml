module D = Domain
module R = Raw
module Q = Quote
module E = Eval
module U = Unify

type ctx = {
  env: D.env;
  lvl: int;
  names: string list;
}
[@@deriving show {with_path = false}]


let empty () = {env = []; lvl = 0; names = []}

let bind (ctx: ctx) (nm: string) (ty: D.t) =
  {env = (ty, None) :: ctx.env; lvl = ctx.lvl + 1; names = nm :: ctx.names}

let define ctx nm ty body =
  {env = (ty, Some body) :: ctx.env; lvl = ctx.lvl + 1; names = nm :: ctx.names}

let nf_r ctx r = Q.quote ctx.lvl (E.eval ctx.env r)
let nf_d ctx d = E.eval ctx.env (Q.quote ctx.lvl d)

let rec check (ctx: ctx) (r: R.t) (ty: D.t): unit =
  print_newline ();
  print_endline "check:";
  print_endline (show_ctx ctx);
  R.print ctx.names r;
  D.print ty;
  match r, ty with
  | Lam (nm, _ty, t), Pi (_, a, bc) ->
    let ctx' = bind ctx nm a in
    check ctx' t (E.inst_clo bc (Local ((Lvl ctx.lvl), [])))
  | Let (nm, letty, e, b), ty ->
    begin match letty with
      | None ->
        let e' = infer ctx e in
        let evald = E.eval ctx.env e in
        check (define ctx nm e' evald) b ty
      | Some t ->
        check ctx t Univ;
        let letty_asv = E.eval ctx.env t in
        check ctx e letty_asv;
        let evald = E.eval ctx.env e in
        check (define ctx nm letty_asv evald) b ty
    end
  | Hole, _t -> failwith "holes"
  | expr, actual ->
    let inferred = infer ctx expr in
    print_endline "\nunify not working the following should be the same";
    D.print actual;
    D.print inferred
    
      
and infer (ctx: ctx) (r: R.t): D.t =
  print_newline ();
  print_endline "infer:";
  print_endline (show_ctx ctx);
  R.print ctx.names r;
  match (r : R.t) with
  | R.Local (Ix i) ->
    let q = D.get_ty @@ D.index ctx.env i in
    print_int i;
    print_string " => ";
    D.print q;
    print_newline();
    q
  | R.Hole -> failwith "holes"
  | R.Let (nm, tyopt, a, b) ->
    begin match tyopt with
      | None ->
        let inf = infer ctx a in
        let a' = E.eval ctx.env a in
        infer (define ctx nm inf a') b
      | Some t ->
        let chk = E.eval ctx.env t in
        check ctx a chk;
        let a' = E.eval ctx.env a in
        infer (define ctx nm chk a') b
    end
  | R.Lam (_, None, _) -> failwith "holes"
  | R.Lam (nm, Some t, b) ->
    let t' = E.eval ctx.env t in
    let b't = Q.quote ctx.lvl @@ infer (bind ctx nm t') b in
    Pi("lam", t', {env = ctx.env; tm = b't})
  | R.App (a, b) ->
    begin match infer ctx a with
      | Pi (_nm, aty, bty) ->
        check ctx b aty;
        let b' = E.inst_clo bty (E.eval ctx.env b) in
        b'
      | _ -> failwith "can't call non-pi"
    end 
  | R.Sigma (nm, a, b)
  | R.Pi (nm, a, b) ->
    check ctx a Univ;
    let a' = E.eval ctx.env a in
    let ctx' = bind ctx nm a' in
    check ctx' b Univ;
    Univ
  | R.Pair (a, b) ->
    let a' = infer ctx a in
    let b' = Q.quote ctx.lvl @@ infer ctx b in
    D.Sigma ("fake", a', {env = ctx.env; tm = b'})
  | R.Proj1 p ->
    begin match infer ctx p with
      | Sigma (_, a, _b) -> a
      | _ -> failwith "can't proj1 from non-sigma"
    end 
  | R.Proj2 p ->
    begin match infer ctx p with
      | Sigma (nm, a, b) ->
        let c = E.inst_clo b a in
        let q = Q.quote ctx.lvl c in
        infer (bind ctx nm a) q
      | _ -> failwith "can't proj2 from non-sigma"
    end
  | R.Univ -> Univ
