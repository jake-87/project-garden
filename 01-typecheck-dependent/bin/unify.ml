module D = Domain
module R = Raw


let rec unify_d lvl (c1: D.t) (c2: D.t): unit =
  match c1, c2 with
  | Stuck q, Stuck w -> unify_stuck lvl q w
  | Lam (nm1, clo1), Lam (nm2, clo2) ->
    unify_clo (lvl + 1) clo1 clo2
  | Pair(a, b), Pair(q, w) ->
    unify_d lvl a q;
    unify_d lvl b w
  | Pi (nm1, b1, clo1), Pi(nm2, b2, clo2)
  | Sigma(nm1, b1, clo1), Sigma(nm2, b2, clo2) ->
    unify_d lvl b1 b2;
    unify_clo (lvl + 1) clo1 clo2
  | Univ, Univ -> ()
  | _, _ ->
    print_endline "\nbad:";
    D.print c1;
    D.print c2;
    failwith "can't unify";

and unify_stuck lvl (s1: D.stuck) (s2: D.stuck) =
  match s1, s2 with
  | Var i, Var j -> assert (i = j)
  | Fst q, Fst w -> unify_stuck lvl q w
  | Snd q, Snd w -> unify_stuck lvl q w
  | App {fn = fn1; arg = arg1},
    App {fn = fn2; arg = arg2} ->
    unify_stuck lvl fn1 fn2;
    unify_d lvl arg1 arg2
  | _, _ ->
    print_endline "\nbad:";
    D.pprint_stuck Format.std_formatter s1;
    D.pprint_stuck Format.std_formatter s2;
    Format.print_newline();
    failwith "can't unify stucks"

and unify_clo (lvl: int) (c1: D.clo) (c2: D.clo) =
  let e1 = Eval.inst_clo c1 (D.Stuck (D.Var (Lvl lvl))) in
  let e2 = Eval.inst_clo c2 (D.Stuck (D.Var (Lvl lvl))) in
  unify_d lvl e1 e2

let unify = unify_d
