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
  print_endline "eval";
  D.pp_env' env;
  S.pp [] tm;
  print_endline "-----";
  match tm with
  | S.Local ix ->
    let (_, dom) = D.index env ix in dom
  | S.Let (_nm, _typ, head, body) -> eval (D.add env Defined (eval env head)) body
  | S.Letrec (_nm, _typ, head, body) ->
    (* this is probably not correct *)
    let env1 = D.add env Defined (D.Stuck {tm = Local (Lvl (D.size env)); elims = []}) in
    print_endline "letrec eval";
    let head1 = eval env1 head in
    print_endline "head1:";
    D.pp head1;
    let head2 = eval (D.add env Defined head1) head in
    print_endline "head2:";
    D.pp head2;
    eval (D.add env Defined head2) body
  | S.Lam (nm, t, i) -> D.Lam (nm, D.{tm = t; env}, i)
  | S.Ap (a, b, i) ->
    print_endline "eval ap:";
    D.pp_env' env;
    S.pp [] a;
    S.pp [] b;
    print_endline "----";
    let a' = eval env a in
    print_endline "got a:";
    D.pp a';
    print_endline "----";
    let b' = eval env b in
    print_endline "got b:";
    D.pp b';
    print_endline "----";
    (match simpl_stuck env a' with
     | D.Lam (_nm, bd, _) -> inst_clo bd D.Bound b'
     | D.Stuck s -> D.Stuck (D.add_elim s (D.Ap (b', i)))
     | _ -> H.cannot "impossible"
    )
  | S.Pair (a, b) -> pair (eval env a) (eval env b)
  | S.First f ->
    let f' = eval env f in
    (match simpl_stuck env f' with
     | D.Pair (a, _) -> a
     | D.Stuck s -> D.Stuck (D.add_elim s (D.First))
     | _ -> H.cannot "impossible"
    )
  | S.Second f ->
    let f' = eval env f in
    (match simpl_stuck env f' with
     | D.Pair (_, b) -> b
     | D.Stuck s -> D.Stuck (D.add_elim s (D.Second))
     | _ -> H.cannot "impossible"
    )
  | S.Pi (nm, S.Impl, a, b) -> ipi nm (eval env a) (clo b env)
  | S.Pi (nm, S.Expl, a, b) ->  pi nm (eval env a) (clo b env)
  | S.Sg (nm, a, b) -> sg nm (eval env a) (clo b env)
  | S.Meta m -> D.Stuck (app_bds env D.{tm = D.Meta m; elims = []})
  | S.Univ -> D.Univ

and app_bds (env: D.env) (m: D.stuck): D.stuck =
  match env with
  | [] -> m
  | (Bound, d) :: xs -> D.add_elim (app_bds xs m) (D.Ap (d, Expl))
  | (Defined, _d) :: xs -> app_bds xs m

and inst_clo (clo: D.clo) (bd: D.bd) (new': D.dom) =
  print_endline "inst_clo";
  D.pp_clo Format.std_formatter clo; Format.print_flush (); print_newline ();
  D.pp new';
  print_endline "----";
  eval (D.add clo.env bd new') clo.tm

and simpl_stuck env tm =
  match tm with
  | D.Stuck {tm = Local (Lvl l); elims = []} ->
    let Ix ix = Debru.lvl2ix (Lvl (D.size env)) (Lvl l) in
    print_endline "simpl_stuck";
    D.pp_env' env;
    print_endline (string_of_int ix);
    print_endline (string_of_int l);
    print_endline (string_of_int (D.size env));
    print_endline "----";
    H.sorry "help"
  | t -> t
