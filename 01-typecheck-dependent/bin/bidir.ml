module D = Domain
module R = Raw
module Q = Quote
module E = Eval
module U = Unify

type bd =
  | Bound
  | Defined
[@@deriving show {with_path = false}]

type env = {
  tms: D.env;
  tys: D.env;
  bds: bd list;
  lvl: int;
  names: string list;
}
[@@deriving show {with_path = false}]

    
let empty () =
  {tms = []; tys = []; lvl = 0; names = []; bds = []}

let define ctx tm ty name =
  {tms = tm :: ctx.tms; tys = ty :: ctx.tys; lvl = ctx.lvl + 1;
   names = name :: ctx.names;
  bds = Defined :: ctx.bds}

let bind ctx ty name =
  {tms = (D.Stuck (D.Var (Lvl ctx.lvl))) :: ctx.tms; tys = ty :: ctx.tys; lvl = ctx.lvl + 1;
   names = name :: ctx.names;
   bds = Bound :: ctx.bds}

let filter ctx: D.env =
  List.combine ctx.tms ctx.bds
  |> List.filter (fun (_tm, bd) ->
      match bd with
      | Bound -> true
      | Defined -> false
    )
  |> List.map fst

let get_ty_ix env ix =
  D.index env.tys ix

let rec check (env: env) (tm: R.t) (ty: D.t): unit =
  print_endline "check";
  match (tm, ty) with
  | Let(nm, Some t, a, e), ty ->
    let t' = E.eval env.tms t in
    check env a t';
    let a' = E.eval env.tms a in
    let env' = define env a' t' nm in
    check env' e ty
  | Let(nm, None, a, e), ty ->
    let ra, t = infer env a in
    let a' = E.eval env.tms ra in
    let env' = define env a' t nm in
    check env' e ty
  | Lam(nm, Some _t, e), Pi(_pi_nm, fn, out) ->
    let env' = bind env fn nm in
    let clo = E.inst_clo out (Stuck (Var (Lvl env.lvl))) in
    check env' e clo
  | Lam(nm, None, e), Pi(_pi_nm, fn, out) ->
    let env' = bind env fn nm in
    let clo = E.inst_clo out (Stuck (Var (Lvl env.lvl))) in
    check env' e clo
  | tm, want ->
    let _tm', got = infer env tm in
    U.unify (filter env) env.lvl want got
    
and infer (env: env) (tm: R.t): R.t * D.t =
  print_endline " infer";
  match tm with
  | Local (Ix i) ->
    tm, get_ty_ix env i  
  | Let(nm, Some t, a, e) ->
    let t' = E.eval env.tms t in
    check env a t';
    let a' = E.eval env.tms a in
    infer (define env a' t' nm) e
  | Let(nm, None, a, e) ->
    let _, aty = infer env a in
    let a' = E.eval env.tms a in
    infer (define env a' aty nm) e
  | Lam(nm, Some t, e) ->
    let t' = E.eval env.tms t in
    let e', ety = infer (bind env t' nm) e in
    let ety' = Q.quote env.lvl ety in
    Lam(nm, Some t, e'), Pi("_", t', {env = env.tms; tm = ety'})
  | Lam(_nm, None, _e) -> failwith "lam inference needs holes"
  | App(a, b) ->
    let a', aty = infer env a in
    let b', bty = infer env b in
    begin match aty with
      | Pi(_nm, fn, out) ->
        U.unify (filter env) env.lvl fn bty;
        App(a', b'), E.inst_clo out (E.eval env.tms b')
      | _ ->
        print_endline "\nbad:";
        D.print aty;
        failwith "can't apply to non-pi"
    end
  | Pi(nm, fn, out) ->
    check env fn Univ;
    let fn' = E.eval env.tms fn in
    let env' = bind env fn' nm in
    check env' out Univ;
    Pi(nm, fn, out), Univ
  | Meta m -> tm, D.Stuck (D.Meta m)
  | InsertedMeta m -> tm, D.Stuck (D.Meta m)
  | Pair _ | Proj1 _ | Proj2 _ | Sigma _ -> failwith "sigma can wait"
  | Univ -> Univ, Univ
      
let infer' (tm: R.t): R.t * D.t =
  infer (empty ()) tm
