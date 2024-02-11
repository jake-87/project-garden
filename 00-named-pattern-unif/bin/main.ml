
let (<|) f x = f x

exception Bad of string
    let bad x = raise <| Bad x

type 'a rev =
  | (::) of 'a rev * 'a
  | []
[@@deriving show {with_path = false}]


let rec tolist = function
  | rest :: x -> List.(x :: (tolist rest))
  | [] -> List.([])

let rec fromlist = function
  | List.(::) (x, xs) -> (fromlist xs) :: x
  | List.([]) -> []

let applist f x =
  fromlist (f (tolist x))

let appnonlist f x =
  f (tolist x)

type metavar = int
  [@@deriving show {with_path = false}]

  
and metaentry =
  | Solved of value
  | Unsolved
[@@deriving show {with_path = false}]


and name = string
[@@deriving show {with_path = false}]


and raw =
  | RRaw of name
  | RLam of name * raw
  | RApp of raw * raw
  | RU
  | RPi of name * raw * raw
  | RLet of name * raw * raw * raw
  | RHole
[@@deriving show {with_path = false}]


and ty = tm
[@@deriving show {with_path = false}]


and bd = Bound of value
       | Defined of value
[@@deriving show {with_path = false}]


and tm =
  | Var of name
  | Lam of name * tm
  | App of tm * tm
  | U
  | Pi of name * ty * ty
  | Let of name * ty * tm * tm
  | Meta of metavar
  | InsertedMeta of metavar * bd rev
[@@deriving show {with_path = false}]


and value =
  | VFlex of metavar * spine
  | VRigid of name * spine
  | VLam of name * closure
  | VPi of name * vty * closure
  | VU
[@@deriving show {with_path = false}]


and env = (name * value) rev
[@@deriving show {with_path = false}]

and spine = value rev
[@@deriving show {with_path = false}]

and closure = Closure of env * tm
[@@deriving show {with_path = false}]

and vty = value
[@@deriving show {with_path = false}]

(* bound helpers *)

(* yes, this is O(n) - TODO improve time complexity
   debrujin is absolutely faster here
*)
let rec is_bound (n: value) (b: bd rev): bool =
  let go b =
    match b with
    | Bound b -> b = n
    | Defined _ -> false
  in
  applist (List.map go) b
  |> appnonlist (List.mem true)

(* env helpers
   we handle envs differently to Andras due to
   the use of names - this is once again not very efficient
*)

let lookupEnv (e: env) (s: name) = 
  let l = tolist e in
  match List.assoc_opt s l with
  | Some v -> v
  | None -> VRigid (s, [])

(* Metavariable handling *)

let metactx: (metavar, metaentry) Hashtbl.t = (Hashtbl.create 20)

let counter = ref 0
let newint () =
  incr counter;
  !counter

let nextMeta = 
  newint

let lookupMeta m =
  match Hashtbl.find_opt metactx m with
  | Some n -> n
  | None -> bad "nometa"

let reset () =
  Hashtbl.clear metactx

let freshMeta (bd: bd rev) =
  let i = nextMeta () in
  Hashtbl.add metactx i Unsolved;
  InsertedMeta (i, bd)

let freshMetaRaw () =
  let i = nextMeta () in
  Hashtbl.add metactx i Unsolved;
  i

let setMeta (m: metavar) (s: metaentry) =
  Hashtbl.replace metactx m s

let showmetas f =
  Hashtbl.iter
    f metactx

(* value evaluation *)

let rec closure (Closure (env, t)) (s: name) (u: value) = eval (env :: (s, u)) t

and evalclos (Closure (env, t)) = eval env t

and vApp (t: value) (u: value): value =
  match t with
  | VLam (s, t) -> closure t s u
  | VFlex (m, sp) -> VFlex (m, sp :: u)
  | VRigid (x, sp) -> VRigid (x, sp :: u)
  | x ->
    print_endline (show_value x);
    bad "impossible vapp"

and vAppSp (v: value) (sp: spine): value =
  match sp with
  | [] -> v
  | env :: t -> vApp (vAppSp t env) t

and vMeta (m: metavar): value =
  match lookupMeta m with
  | Solved v -> v
  | Unsolved -> VFlex (m, [])

and vAppBDs (e: env) (v: value) (bd: bd rev): value =
  match e with
  | rest :: t ->
    if is_bound (snd t) bd then
      vApp (vAppBDs rest v bd) (snd t)
    else
      vAppBDs rest v bd
  | [] -> v

and eval (e: env) (t: tm): value =
  match t with
  | Var s -> lookupEnv e s
  | Lam (nm, ty) -> VLam (nm, Closure (e, ty))
  | App (a, b) -> vApp (eval e a) (eval e b)
  | U -> VU
  | Pi (name, a, b) -> VPi (name, eval e a, Closure (e, b))
  | Let (name, _ty, a, b) -> eval (e :: (name, eval e a)) b 
  | Meta m -> VFlex (m, [])
  | InsertedMeta (m, bds) -> vAppBDs e (VFlex (m, [])) bds

let rec force (v: value): value =
  match v with
  | VFlex (m, sp) ->
    begin
      match lookupMeta m with
      | Solved t -> force (vAppSp t sp)
      | _ -> v
    end
  | _ -> v

let rec quoteSpine (v: tm) (s: spine): tm =
  match s with
  | [] -> v
  | rest :: x -> App ((quoteSpine v rest), (quote x))

and quote (v: value): tm =
  match force v with
  | VFlex (m, sp) -> quoteSpine (Meta m) sp
  | VRigid (x, sp) -> quoteSpine (Var x) sp
  | VLam (name, t) -> Lam (name, quote (closure t name (VRigid (name, []))))
  | VPi (name, a, b) -> Pi (name, quote a, quote (closure b name (VRigid (name, []))))
  | VU -> U

and nf (e: env) (t: tm): tm =
  quote (eval e t)

(* unification *)
exception UnifyErr

let rec occursSp (m: metavar) (t: tm) (b: name rev) (sp: spine): tm =
  match sp with 
  | [] -> t
  | sp :: x -> App (occursSp m t b sp, occurs m b x) 

and occurs (m: metavar) (b: name rev) (v: value): tm =
  match v with
  | VFlex (mt, sp) ->
    if
      m <> mt
    then
      occursSp m (Meta mt) b sp
    else
      (* occurs check failure *)
      raise <| UnifyErr
  | VRigid (mt, sp) ->
    if
      appnonlist (List.exists (fun x -> x = mt)) b
    then
      occursSp m (Var mt) b sp
    else
      (* not in spine, scope check failure *)
      raise UnifyErr
  | VLam (name, clos) -> Lam (name, occurs m b (closure clos name (VRigid(name, []))))
  | VPi (name, vty, clos) ->
    Pi (name, occurs m b vty, occurs m b (closure clos name (VRigid(name, []))))
  | VU -> U

let rec lams (b: name rev) (t: tm) =
  match b with
  | [] -> t
  | r :: x -> Lam(x, lams r t)

let solve (m: metavar) (b: name rev) (v: value) =
  print_endline "solving:";
  print_endline (show_value v);
  let rhs = occurs m b v in
  let solution = eval [] rhs in
  print_endline "got: ";
  print_endline (show_vty solution);
  print_endline "\n\n";
  setMeta m (Solved solution)

let rec subst (old: name) (new': name) (v: vty) =
  match v with
  | VFlex (m, sp) -> VFlex(m, applist (List.map <| subst old new') sp)
  | VRigid (x, sp) ->
    if x = old then
      VRigid(new', applist (List.map <| subst old new') sp)
    else 
      VRigid(x, applist (List.map <| subst old new') sp)
  | VLam (n, Closure(env, tm)) ->
    let env' = applist (List.map <| (fun (a, b) -> (a, subst old new' b))) env in
    if n <> old then
      let tm' = subst old new' (eval [] tm) in
      VLam(n, Closure(env', quote tm'))
    else
      VLam(n, Closure(env', tm))
  | VPi (n, vty, Closure(env, tm)) ->
    let env' = applist (List.map <| (fun (a, b) -> (a, subst old new' b))) env in
    let vty' = subst old new' vty in
    if n <> old then
      let tm' = subst old new' (eval [] tm) in
      VPi(n, vty', Closure(env', quote tm'))
    else
      VPi(n, vty',  Closure(env', tm))
  | VU -> VU

let rec unifySp (b: name rev) (sp1: spine) (sp2: spine) =
  match sp1, sp2 with
  | [], [] -> ()
  | sp :: t, sp' :: t' ->
    unify b t t';
    unifySp b sp sp'
  | _, _ -> raise UnifyErr
 
and unify (names: name rev) (v1: vty) (v2: vty) =
  print_endline "unifing:";
  print_endline (show_vty v1);
  print_endline (show_vty v2);
  print_endline "\n\n";
  match force v1, force v2 with
  | VLam(n, c), VLam(n', c') ->
    let c' = subst n' n (evalclos c') in
    unify (names :: n) (evalclos c) c'
  | VLam(n, c), t
  | t, VLam(n, c) -> unify (names :: n) (vApp t (VRigid (n, []))) (closure c n (VRigid (n, [])))
  | VU, VU -> ()
  | VPi(x, a, b), VPi(x', a', b') ->
    let b' = subst x' x (evalclos b') in
    unify names a a';
    unify (names :: x) (evalclos b) b'
  | VRigid(x, sp), VRigid(x', sp') ->
    if x = x' then
      unifySp (names :: x) sp sp'
    else
      raise UnifyErr
  | VFlex(m, sp), VFlex(m', sp') ->
    if m = m' then
      unifySp names sp sp'
    else
      raise UnifyErr
  | VFlex (m, _sp), t
  | t, VFlex (m, _sp) ->
    solve m names t
  | _, _ -> raise UnifyErr

let () =
  let a = Lam("a", Var("a")) in
  let b = Lam("b", freshMeta []) in
  let a' = eval [] a in
  let b' = eval [] b in
  print_endline (show_value a');
  print_endline (show_value b');
  begin
    try
      unify [] a' b';
    with
    | UnifyErr ->
      failwith "couldn't unify"
  end;
  print_endline (show_ty <| quote a');
  print_endline (show_ty <| quote b');
  showmetas (fun a b ->
      print_int a;
      print_string ": ";
      print_endline <|
      match b with
      | Unsolved -> show_metaentry b
      | Solved vty -> show_tm (quote vty)
    );
  print_endline "done"
