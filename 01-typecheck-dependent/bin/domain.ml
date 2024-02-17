type lvl = Lvl of int
[@@deriving show {with_path = false}]

and t =
  | Local of lvl * t list
  (* var * applied to var *)
  | Lam of string * clo
  | Pair of t * t
  | Pi of string * t * clo
  | Sigma of string * t * clo
  | Univ
[@@deriving show {with_path = false}]

and env' = t * t option [@printer fun fmt t ->
    match snd t with
    | None -> Format.fprintf fmt "@[%a@] <no bod>" pp (fst t)
    | Some _ -> 
      Format.fprintf fmt "@[%a@] <bod>" pp (fst t)
  ]

and env = env' list

(* type * optional body (mostly for lets) *)

and clo = { tm : Raw.t; env: env }
[@@deriving show {with_path = false}]


let empty : env = []
let extend (env: env) (v: t * t option): env =
  v :: env

let index (env : env) (ix : int) =
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
  | Local ((Lvl i), t) ->
    if t = [] then
      Format.fprintf fmt "#%i" i
    else 
      Format.fprintf fmt "#%i args: %a" i pprint_varl t
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

let print tm =
  pprint Format.std_formatter tm;
  Format.print_newline();
