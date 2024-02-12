type t =
  | Local of int
  | Lam of string * clo
  | Pair of t * t
  | Pi of string * t * clo
  | Sigma of string * t * clo
  | Univ
[@@deriving show {with_path = false}]

and env = t list
[@@deriving show {with_path = false}]

and clo = { tm : Raw.t; env: env }
[@@deriving show {with_path = false}]


let empty : env = []
let extend (env: env) (v: t): env =
  v :: env
  
let index (env : env) (ix : int) =
  try
    List.nth env ix
  with
  | Failure _ ->
    failwith "nth failed in Domain.index"
       
let size (env : env) : int =
  List.length env

let rec pprint (fmt: Format.formatter) (tm: t) : unit =
  match tm with
  | Local i -> Format.fprintf fmt "#%i" i
  | Lam (a, clo) -> Format.fprintf fmt "@[λ%s. %a@]" a pprint_clo clo
  | Pair (a, b) -> Format.fprintf fmt "@[(%a, %a)@]" pprint a pp b
  | Pi (nm, a, clo) -> Format.fprintf fmt "@[Π(%s : %a)@] -> %a" nm pprint a pprint_clo clo
  | Sigma (nm, a, clo) -> Format.fprintf fmt "@[Σ(%s : %a)@] × %a" nm pprint a pprint_clo clo
  | Univ -> Format.fprintf fmt "Univ"

and pprint_clo  (fmt: Format.formatter) (clo: clo) =
  let {tm; env = _env} = clo in
  Format.fprintf fmt "@[(clo) %a@]" (Raw.pprint []) tm

let print tm =
  pprint Format.std_formatter tm;
  Format.print_newline();
