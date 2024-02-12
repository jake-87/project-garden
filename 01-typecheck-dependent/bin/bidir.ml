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
  {env = ty :: ctx.env; lvl = ctx.lvl + 1; names = nm :: ctx.names}

let define = bind

let rec check (ctx: ctx) (r: R.t) (ty: D.t): unit =
  print_newline ();
  print_endline "check:";
  print_endline (show_ctx ctx);
  R.print ctx.names r;
  D.print ty;
  match r, ty with
  | Lam (nm, _ty, t), Pi (_, a, bc) ->
    let ctx' = bind ctx nm a in
    check ctx' t (E.inst_clo bc (Local ctx.lvl))
  | Let (nm, letty, e, b), ty ->
    begin match letty with
      | None ->
        let e' = infer ctx e in
        let e'_asv = E.eval ctx.env e' in
        check (define ctx nm e'_asv) b e'_asv
      | Some t ->
        check ctx t Univ;
        let letty_asv = E.eval ctx.env t in
        check ctx e letty_asv;
        check (define ctx nm letty_asv) b ty
    end
  | Hole, t -> failwith "holes"
  | expr, actual ->
    let inferred = E.eval ctx.env (infer ctx expr) in
    if
      not @@ U.unify ctx.lvl actual inferred
    then
      begin
        D.print actual;
        D.print inferred;
        failwith "actual did not match expected"
      end
      
and infer (ctx: ctx) (r: R.t): R.t =
  print_newline ();
  print_endline "infer:";
  print_endline (show_ctx ctx);
  R.print ctx.names r;
  match (r : R.t) with
  | R.Local i ->
    let q = Q.quote ctx.lvl @@ D.index ctx.env i in
    print_int i;
    print_string " => ";
    R.print ctx.names q;
    print_newline();
    q
  | R.Hole -> failwith "holes"
  | R.Let (nm, tyopt, a, b) ->
    begin match tyopt with
      | None ->
        let inf = E.eval ctx.env @@ infer ctx a in
        infer (define ctx nm inf) b
      | Some t ->
        let chk = E.eval ctx.env t in
        check ctx a chk;
        infer (define ctx nm chk) b
    end
  | R.Lam (_, None, _) -> failwith "holes"
  | R.Lam (nm, Some t, b) ->
    let t' = E.eval ctx.env t in
    let b't = infer (bind ctx nm t') b in
    Pi("lam", t, b't)
      
  | R.App (a, b) ->
    begin match infer ctx a with
      | Pi (_nm, aty, bty) ->
        let aty_v = E.eval ctx.env aty in
        check ctx b aty_v;
        Q.quote ctx.lvl (E.eval ctx.env bty)
      | _ -> failwith "can't call non-pi"
    end 
  | R.Sigma (nm, a, b)
  | R.Pi (nm, a, b) ->
    check ctx a Univ;
    print_endline "WHAT IS IT";
    R.print ctx.names a;
    R.print [] a;
    print_endline (show_ctx ctx);
    let a' = E.eval ctx.env a in
    D.print a';
    print_endline "no more yelling";
    let ctx' = bind ctx nm a' in
    check ctx' b Univ;
    Univ
  | R.Pair (a, b) ->
    let a' = infer ctx a in
    let b' = infer ctx b in
    R.Sigma ("fake", a', b')
  | R.Proj1 p ->
    begin match infer ctx p with
      | Sigma (_, a, _b) -> a
      | _ -> failwith "can't proj1 from non-sigma"
    end 
  | R.Proj2 p ->
    begin match infer ctx p with
      | Sigma (nm, a, b) ->
        infer (bind ctx nm (E.eval ctx.env @@ infer ctx a)) b
      | _ -> failwith "can't proj2 from non-sigma"
    end
  | R.Univ -> Univ
