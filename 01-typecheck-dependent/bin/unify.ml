module D = Domain
module R = Raw
module P = Partial

let rec unify_d bounds lvl (c1: D.t) (c2: D.t): unit =
  match c1, c2 with
  | Stuck (Meta m), t
  | t, Stuck (Meta m) ->
    failwith "metas unify"
  | Stuck q, Stuck w -> unify_stuck bounds lvl q w
  | Lam (_nm1, clo1), Lam (_nm2, clo2) ->
    unify_clo bounds (lvl + 1) clo1 clo2
  | Pair(a, b), Pair(q, w) ->
    unify_d bounds lvl a q;
    unify_d bounds lvl b w
  | Pi (_nm1, b1, clo1), Pi(_nm2, b2, clo2)
  | Sigma(_nm1, b1, clo1), Sigma(_nm2, b2, clo2) ->
    unify_d bounds lvl b1 b2;
    unify_clo bounds (lvl + 1) clo1 clo2
  | Univ, Univ -> ()
  | _, _ ->
    print_endline "\nbad:";
    D.print c1;
    D.print c2;
    failwith "can't unify";

and unify_stuck bounds lvl (s1: D.stuck) (s2: D.stuck) =
  match s1, s2 with
  | Var i, Var j -> assert (i = j)
  | Fst q, Fst w -> unify_stuck bounds lvl q w
  | Snd q, Snd w -> unify_stuck bounds lvl q w
  | App {fn = fn1; arg = arg1},
    App {fn = fn2; arg = arg2} ->
    unify_stuck bounds lvl fn1 fn2;
    unify_d bounds lvl arg1 arg2
  | Meta m1, Meta m2 ->
    if m1 <> m2 then
      failwith "unifying uneq metas"
    else ()
  | Meta m, t
  | t, Meta m ->
    failwith "metas unify stuck"
  | _, _ ->
    print_endline "\nbad:";
    D.pprint_stuck Format.std_formatter s1;
    D.pprint_stuck Format.std_formatter s2;
    Format.print_newline();
    failwith "can't unify stucks"

and unify_clo bounds (lvl: int) (c1: D.clo) (c2: D.clo) =
  let e1 = Eval.inst_clo c1 (D.Stuck (D.Var (Lvl lvl))) in
  let e2 = Eval.inst_clo c2 (D.Stuck (D.Var (Lvl lvl))) in
  unify_d bounds lvl e1 e2

let unify : D.env -> int -> D.t -> D.t -> unit = unify_d
