type lvl = Lvl of int
[@@deriving show {with_path = false}]

and t =
  | Stuck of stuck
             (* stuck * type *)
  | Lam of string * clo
  | Pair of t * t
  | Pi of string * t * clo
  | Sigma of string * t * clo
  | Univ
[@@deriving show {with_path = false}]

and env = t list

and stuck =
  | Var of lvl
  | Fst of stuck
  | Snd of stuck
  | App of {fn: stuck; arg: t}

(* type * optional body (mostly for lets) *)

and clo = { tm : Raw.t; env: env }
[@@deriving show {with_path = false}]


let empty : env = []
let extend env v =
  v :: env

let index env (ix : int) =
  try
    List.nth env ix
  with
  | Failure _ ->
    failwith "nth failed in Domain.index"

let get_ty = fst
let get_body = snd

let size (env : env) : int =
  List.length env

let rec pprint (fmt: Format.formatter) (tm: t) : unit =
  match tm with
  | Stuck t -> Format.fprintf fmt "@[stuck: %a@]" pprint_stuck t
  | Lam (a, clo) -> Format.fprintf fmt "@[λ%s. %a@]" a pprint_clo clo
  | Pair (a, b) -> Format.fprintf fmt "@[(%a, %a)@]" pprint a pprint b
  | Pi (nm, a, clo) -> Format.fprintf fmt "@[Π(%s : %a)@] -> %a" nm pprint a pprint_clo clo
  | Sigma (nm, a, clo) -> Format.fprintf fmt "@[Σ(%s : %a)@] × %a" nm pprint a pprint_clo clo
  | Univ -> Format.fprintf fmt "Univ"

and pprint_varl fmt l =
  match l with
  | [] -> ()
  | x :: xs ->
    pprint_varl fmt xs;
    Format.fprintf fmt "@[[%a] @]" pprint x
    

and pprint_clo  (fmt: Format.formatter) (clo: clo) =
  let {tm; env = _env} = clo in
  Format.fprintf fmt "@[(clo) %a@]" (Raw.pprint []) tm

and pprint_stuck (fmt: Format.formatter) (s: stuck) =
  match s with
  | Var (Lvl i) -> Format.fprintf fmt "@[lvl %i@]" i
  | Fst s -> Format.fprintf fmt "@[fst (%a)@]" pprint_stuck s
  | Snd s -> Format.fprintf fmt "@[snd (%a)@]" pprint_stuck s
  | App {fn; arg} -> Format.fprintf fmt "@[%a (%a)@]"
                                pprint_stuck fn
                                pprint arg

let print tm =
  pprint Format.std_formatter tm;
  Format.print_newline();
