type ix = Ix of int
let unix (Ix i) = i
module M = Metas
(* somewhat user facing syntax, using debrujin indecies *)

type syn =
  | Local of ix
  (* let name : t = b in x*)
  | Let of string * syn * syn * syn
  | Lam of string * syn
  | Ap of syn * syn
  | Pair of syn * syn
  | First of syn
  | Second of syn
  | Pi of string * syn * syn
  | Sg of string * syn * syn
  | Meta of M.meta
  | Univ

type 'a ix_env = 'a list

let ix_lookup (Ix i) (env: 'a ix_env) = List.nth env i   

let ix_add (x: 'a) (env: 'a ix_env) = x :: env


let rec pp_syn (pp_env : string ix_env) (fmt: Format.formatter) (tm: syn) =
  match tm with
  | Local ix ->
    begin try
        Format.fprintf fmt "%s" (ix_lookup ix pp_env)
      with
            | Failure _ ->
        Format.fprintf fmt "#%i" (unix ix)
    end 
  | Let (nm, typ, head, body) -> Format.fprintf fmt "let %s : %a = %a in\n%a"
                                   nm
                                   (pp_syn pp_env)
                                   typ
                                   (pp_syn pp_env)
                                   head
                                   (pp_syn (ix_add nm pp_env))
                                   body
  | Lam (nm, body) -> Format.fprintf fmt "λ%s. %a"
                        nm
                        (pp_syn (ix_add nm pp_env))
                        body
  | Ap (f, Ap (g, x)) ->
    Format.fprintf fmt "%a (%a)"
                   (pp_syn pp_env) f 
                   (pp_syn pp_env) (Ap (g, x))
  | Ap (f, x) -> Format.fprintf fmt "%a %a"
                   (pp_syn pp_env) f 
                   (pp_syn pp_env) x
  | Pair (a, b) -> Format.fprintf fmt "(%a, %a)"
                     (pp_syn pp_env) a
                     (pp_syn pp_env) b
  | First a -> Format.fprintf fmt "%a .fst" (pp_syn pp_env) a
  | Second a -> Format.fprintf fmt "%a .snd" (pp_syn pp_env) a
  | Pi ("_", a, b) -> Format.fprintf fmt "%a -> %a"
                        (pp_syn pp_env)
                        a
                        (pp_syn (ix_add "_" pp_env))
                        b
  | Pi (nm, a, b) -> Format.fprintf fmt "Π (%s : %a) -> %a"
                       nm
                       (pp_syn pp_env)
                       a
                       (pp_syn (ix_add nm pp_env))
                       b
  | Sg ("_", a, b) -> Format.fprintf fmt "%a ⨉ %a"
                        (pp_syn pp_env)
                        a
                        (pp_syn (ix_add "_" pp_env))
                        b
  | Sg (nm, a, b) -> Format.fprintf fmt "Σ (%s : %a) -> %a"
                       nm
                       (pp_syn pp_env)
                       a
                       (pp_syn (ix_add nm pp_env))
                       b
  | Meta m -> M.pp_meta fmt m
  | Univ -> Format.fprintf fmt "Univ"

and pp_ix_list fmt env =
  match env with
  | [] -> ()
  | (Ix x) :: xs ->
    pp_ix_list fmt xs;
    Format.fprintf fmt "%i" x

let pp env tm =
    pp_syn env Format.std_formatter tm;
    Format.print_newline()

module Constructors = struct
  let local i = Local (Ix i)
  let let_ nm t a b = Let (nm, t, a, b)
  let lam nm b = Lam (nm, b)
  let ap a b = Ap (a, b)
  let pair a b = Pair (a, b)
  let fst a = First a
  let snd b = Second b
  let pi nm a b = Pi (nm, a, b)
  let arr a b = Pi ("_", a, b)
  let sg nm a b = Sg (nm, a, b)
  let u = Univ
end
