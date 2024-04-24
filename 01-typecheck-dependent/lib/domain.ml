(* some helpers *)
type lvl = Lvl of int

let unlvl (Lvl i) = i

let lvlsucc (Lvl i) = Lvl (i + 1)
module M = Metas

(* domain, using debrujin levels *)

(* which terms are bounds (lams, sigmdas, etc) and which are
   defined (let)
*)
type bd = Bound | Defined

type dom =
  | Pair of dom * dom
  | Lam of string * clo 
  | Pi of string * dom * clo
  | Sg of string * dom * clo
  | Stuck of stuck
  | Univ

and clo = {tm: Syntax.syn; env: env}

and stuck = {tm: head; elims: elim list}

and head =
  | Local of lvl
  | Meta of M.meta

and elim =
  | Ap of dom
  | First
  | Second

and env = (bd * dom) list
    
let add_elim (s: stuck) (e: elim) = {tm = s.tm; elims = e :: s.elims}

let rec add_elims (s: stuck) (e: elim list) =
  match e with
  | [] -> s
  | x :: xs ->
    let rest = add_elims s xs in
    add_elim rest x

let rec env_to_nums' env =
  match env with
  | [] -> []
  | _ :: xs ->
    let curr = string_of_int (List.length xs) in
    let rest = env_to_nums' xs in
    curr :: rest

let env_to_nums e = List.rev (env_to_nums' e)

let empty : env = []

let add (env: env) (a: bd) (elm: dom): env = (a, elm) :: env

let index (env: env) (i: Syntax.ix) =
  List.nth env (Syntax.unix i)

let size (env: env) = List.length env

let local (l: lvl) = Stuck {tm = (Local l); elims = []}

let rec pp_dom (fmt: Format.formatter) (tm: dom) =
  match tm with
  | Pair (a, b) -> Format.fprintf fmt "#(%a, %a)"
                     pp_dom a pp_dom b
  | Lam (nm, clo) -> Format.fprintf fmt "#λ%s. %a"
                       nm pp_clo clo
  | Pi (nm, dom, clo) -> Format.fprintf fmt "#Π (%s : %a) -> %a"
                           nm pp_dom dom pp_clo clo
  | Sg (nm, dom, clo) -> Format.fprintf fmt "#Σ (%s : %a) -> %a"
                           nm pp_dom dom pp_clo clo
  | Stuck t -> Format.fprintf fmt "#stuck: %a" pp_stuck t
  | Univ -> Format.fprintf fmt "#U" 

and pp_clo (fmt: Format.formatter) (tm: clo) =
  let {tm; env} = tm in
  Syntax.pp_syn (env_to_nums env) fmt tm 

and pp_stuck (fmt: Format.formatter) (tm: stuck) =
  let {tm; elims} = tm in
  Format.fprintf fmt "%a %a" pp_head tm pp_elims elims

and pp_head (fmt: Format.formatter) (tm: head) =
  match tm with
  | Local (Lvl l) -> Format.fprintf fmt "%i" l
  | Meta m -> M.pp_meta fmt m

and pp_elims (fmt: Format.formatter) (e: elim list) =
  match e with
  | [] -> ()
  | x :: xs ->
    pp_elims fmt xs;
    match x with
    | Ap dom -> Format.fprintf fmt " .ap(%a) " pp_dom dom
    | First -> Format.fprintf fmt " .fst "
    | Second -> Format.fprintf fmt " .snd "

and pp_env fmt env =
  Format.fprintf fmt "[";
  List.iter (fun (_a, b) -> Format.fprintf fmt "%a, " pp_dom b) env;
  Format.fprintf fmt "]\n"

let pp_env' env = pp_env Format.std_formatter env

let pp tm = pp_dom Format.std_formatter tm;
  Format.print_newline()


type solver = Unsolved
            | Solved of dom
[@@deriving show {with_path = false}]


module Constructors = struct 
  let pair a b = Pair (a, b)
  let lam s c = Lam (s, c)
  let pi s d c = Pi (s, d, c)
  let sg s d c = Sg (s, d, c)
  let stuck tm elims = Stuck {tm; elims}
  let u = Univ
    
  let clo tm env: clo = {tm; env}
                        
  let local i = Local i
      
  let ap d = Ap d
  let fst = First
  let snd = Second
end
