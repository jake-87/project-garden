
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
  | None -> VVar s

(* Metavariable handling *)

let metactx: (metavar, metaentry) Hashtbl.t = (Hashtbl.create 20)

let counter = ref 0
let newint () =
  let t = !counter in
  incr counter;
  t

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

(* value evaluation *)

let rec closure (Closure (env, t)) (s: name) (u: value) = eval (env :: (s, u)) t

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
  | Unsolved -> VFlex m []

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
  | Meta m -> VFlex m []
  | InsertedMeta (m, bds) -> vAppBDs e (VFlex m []) bds

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
  | VLam (name, t) -> Lam (name, quote (closure t name (VVar name)))
  | VPi (name, a, b) -> Pi (name, quote a, quote (closure b name (VVar name)))
  | VU -> U

and nf (e: env) (t: tm): tm =
  quote (eval e t)

let () =
  let a = Let ("x", U, Var "y", App (freshMeta [], (Var "x"))) in
  print_endline (show_tm (nf [] a))
