module H = Helpers
module S = Syntax
module B = Bidir
module M = Metas
module D = Domain


type raw =
  | Local of string
  | Let of string * raw * raw * raw
  | Letrec of string * raw * raw * raw
  | Lam of string * S.icit * raw
  | Ap of raw * raw * S.icit
  | Pair of raw * raw
  | First of raw
  | Second of raw
  | Pi of string * S.icit * raw * raw
  | Sg of string * raw * raw
  | Hole
  | Univ
[@@deriving show {with_path = false}]

let pp r = pp_raw Format.std_formatter r;
  Format.print_flush();
  print_newline();

module Cons = struct
  let l l = Local l
  let let_ s a b c = Let(s,a,b,c)
      let letrec s a b c = Letrec(s,a,b,c)
  let lam s r = Lam(s, S.Expl, r)
  let ap a b = (Ap (l a, l b, S.Expl))
  let ap2 a b = Ap(a,b, S.Expl)
  let ap3 a b c = (Ap(Ap(a,b, S.Expl),c, S.Expl))
  let ap4 a b c d = Ap(Ap(Ap(a,b, S.Expl),c, S.Expl),d, S.Expl)
  let ap5 a b c d e = Ap(Ap(Ap(Ap(a,b, S.Expl),c, S.Expl),d, S.Expl),e, S.Expl)
  let pair a b = Pair(a,b)
  let first a = First a
  let second b = Second b
  let pi s a b = Pi(s,S.Expl,a,b)
  let arr a b = Pi("_",S.Expl,a,b)

  let ilam s r = Lam(s,S.Impl,r)
  let ipi nm a b = Pi(nm,S.Impl,a,b)
  let iapp a b = Ap(a,b,S.Impl)
  
  let sg s a b = Sg(s,a,b)
  let hole = Hole
  let u = Univ
end 

let unwrap (u: 'a option): 'a =
  match u with
  | None -> H.sorry "unwrap"
  | Some i -> i

let rec elab (mctx: B.ctx) (ctx: string list) (r: raw): S.syn =
  match r with
  | Local s -> S.Local (S.Ix (unwrap (List.find_index ((=) s) ctx)))
  | Let (nm, typ, head, tail) ->
    let typ' = elab mctx ctx typ in
    let head' = elab mctx ctx head in
    let tail' = elab mctx (nm :: ctx) tail in
    S.Let (nm, typ', head', tail')
  | Letrec (nm, typ, head, tail) ->
    let typ' = elab mctx ctx typ in
    let head' = elab mctx (nm :: ctx) head in
    let tail' = elab mctx (nm :: ctx) tail in
    S.Letrec(nm, typ', head', tail')
  | Lam (nm, i, body) ->
    S.Lam (nm, elab mctx (nm :: ctx) body, i)
  | Ap (a, b, i ) ->
    let b' = elab mctx ctx b in
    S.Ap (elab mctx ctx a, b', i)
  | Pair (a, b) ->
    let b' = elab mctx ctx b in
    S.Pair (elab mctx ctx a, b')
  | First s -> S.First (elab mctx ctx s)
  | Second s -> S.Second (elab mctx ctx s)
  | Pi (nm, i, head, tail) ->
    let tail' = elab mctx (nm :: ctx) tail in
    S.Pi(nm, i, elab mctx ctx head, tail')
  | Sg (nm, head, tail) ->
    let tail' = elab mctx (nm :: ctx) tail in
    S.Sg(nm, elab mctx ctx head, tail')
  | Hole ->
    let m = M.fresh_meta () in
    M.set mctx.metactx m D.Unsolved;
    S.Meta m
  | Univ -> S.Univ
