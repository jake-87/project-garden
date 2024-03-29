module M = Metavar

type ix = Ix of int
[@@deriving show {with_path = false}]

type t =
  | Local of ix
  | Let of string * t option * t * t
  (* ty tm tm *)
  | Lam of string * t option * t
  (* ty tm *)
  | App of t * t
  | Pi of string * t * t
  | Pair of t * t
  | Proj1 of t
  | Proj2 of t
  | Sigma of string * t * t
  | Meta of M.metavar
  | InsertedMeta of M.metavar
  | Univ
[@@deriving show {with_path = false}]


let rec pprint (pp_env: string list) (fmt: Format.formatter) (tm: t) : unit =
  match tm with
  | Local (Ix i) ->
    begin try
        Format.fprintf fmt "%s" (List.nth pp_env i)
      with _ ->
        Format.fprintf fmt "ix #%i" i
    end 
  | Let (nm, None, a, b) ->
    Format.fprintf fmt "@[let %s =@ %a in@ %a@]" nm
      (pprint pp_env) a
      (pprint (nm :: pp_env)) b
  | Let (nm, Some ty, a, b) ->
    Format.fprintf fmt "@[let %s : %a =@ %a in@ %a@]" nm
      (pprint pp_env) ty
      (pprint pp_env) a
      (pprint (nm :: pp_env)) b
  | Lam (x, None, b) ->
    Format.fprintf fmt "@[λ%s. %a@]" x (pprint (x :: pp_env)) b
  | Lam (x, Some ty, b) ->
    Format.fprintf fmt "@[λ%s: %a. %a@]" x (pprint pp_env) ty (pprint (x :: pp_env)) b
  | App (a, b) -> Format.fprintf fmt "%a (%a)" (pprint pp_env) a (pprint pp_env) b
  | Pi ("_", base, fam) ->
    Format.fprintf fmt "@[%a -> %a@]" (pprint pp_env) base (pprint ("_" :: pp_env)) fam
  | Pi (x, base, fam) ->
    Format.fprintf fmt "@[Π(%s : %a)@] -> %a" x (pprint pp_env) base (pprint (x :: pp_env)) fam
  | Pair(a, b) ->
    Format.fprintf fmt "@[(%a, %a)@]" (pprint pp_env) a (pprint pp_env) b
  | Proj1 a -> Format.fprintf fmt "@[ π1 %a @]" (pprint pp_env) a
  | Proj2 a -> Format.fprintf fmt "@[ π2 %a @]" (pprint pp_env) a
  | Sigma (x, base, fam) ->
    Format.fprintf fmt "@[Σ(%s : %a)@] × %a" x (pprint pp_env) base (pprint (x :: pp_env)) fam
  | Meta m -> Format.fprintf fmt "@[!?%i@]" m
  | InsertedMeta m -> Format.fprintf fmt "@[?%i@]" m
  | Univ -> Format.fprintf fmt "Univ"

let print env tm =
  pprint env Format.std_formatter tm;
  Format.print_newline ();
