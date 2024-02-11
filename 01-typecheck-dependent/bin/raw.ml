type t =
  | Local of int
  | Hole
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
  | Univ

let rec pp (pp_env: string list) (fmt: Format.formatter) (tm: t) : unit =
  match tm with
  | Local i ->
    begin try
        Format.fprintf fmt "%s" (List.nth pp_env i)
      with _ ->
        Format.fprintf fmt "#%i" i
    end 
  | Hole -> Format.fprintf fmt "?_"
  | Let (nm, None, a, b) ->
    Format.fprintf fmt "@[let %s = %a in@ %a@]" nm
      (pp pp_env) a
      (pp (nm :: pp_env)) b
  | Let (nm, Some ty, a, b) ->
    Format.fprintf fmt "@[let %s : %a = %a in@ %a@]" nm
      (pp pp_env) ty
      (pp pp_env) a
      (pp (nm :: pp_env)) b
  | Lam (x, None, b) ->
    Format.fprintf fmt "@[λ%s. %a@]" x (pp (x :: pp_env)) b
  | Lam (x, Some ty, b) ->
    Format.fprintf fmt "@[λ%s: %a. %a@]" x  (pp pp_env) ty (pp (x :: pp_env)) b
  | App (a, b) -> Format.fprintf fmt "(%a) (%a)" (pp pp_env) a (pp pp_env) b 
  | Pi (x, base, fam) ->
    Format.fprintf fmt "@[Π(%s : %a)@] -> %a" x (pp pp_env) base (pp (x :: pp_env)) fam
  | Pair(a, b) ->
    Format.fprintf fmt "@[(%a, %a)@]" (pp pp_env) a (pp pp_env) b
  | Proj1 a -> Format.fprintf fmt "@[ π1 %a @]" (pp pp_env) a
  | Proj2 a -> Format.fprintf fmt "@[ π2 %a @]" (pp pp_env) a
  | Sigma (x, base, fam) ->
    Format.fprintf fmt "@[Σ(%s : %a)@] × %a" x (pp pp_env) base (pp (x :: pp_env)) fam
  | Univ -> Format.fprintf fmt "Univ"

let print env tm =
  pp env Format.std_formatter tm;
  Format.print_newline ();
