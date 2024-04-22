module S = Syntax
module D = Domain
module E = Eval
module Q = Quote
module H = Helpers


type ctx = {
  (* Ix indexed (ie new stuff at the front) *)
  names: string list;
  terms: D.env;
  types: D.env;
  lvl: D.lvl;
}

let new_var (ctx: ctx) = 
  D.Stuck {tm = D.Local ctx.lvl; elims = []}

let inst_newvar l a =
  E.inst_clo a (D.Stuck {tm = D.Local l; elims = []})

let empty_ctx () = {
  names = [];
  terms = [];
  types = [];
  lvl = D.Lvl 0;
}

let bind (ctx: ctx) (nm: string) (typ: D.dom) =
  {
    names = nm :: ctx.names;
    terms = D.add ctx.terms (new_var ctx);
    types = D.add ctx.types typ;
    lvl = D.lvlsucc ctx.lvl;
  }

let define (ctx: ctx) (nm: string) (body: D.dom) (typ: D.dom) =
  {
    names = nm :: ctx.names;
    terms = D.add ctx.terms body;
    types = D.add ctx.types typ;
    lvl = D.lvlsucc ctx.lvl;
  }

let rec unify (l: D.lvl) (d1: D.dom) (d2: D.dom): bool =
  match d1, d2 with
  | Pair (a, b), Pair (x, y) ->
    (unify l a x) && (unify l b y)
  | Lam (_, a), Lam(_, b) ->
    unify (D.lvlsucc l) (inst_newvar l a) (inst_newvar l b)
  | Sg (_, a, clo), Sg (_, b, clo2)
  | Pi (_, a, clo), Pi (_, b, clo2) ->
    unify l a b && unify (D.lvlsucc l) (inst_newvar l clo) (inst_newvar l clo2)
  | Stuck {tm; elims}, Stuck {tm=tm2; elims=elims2} ->
    unifyHead l tm tm2
    && unifySpine l elims elims2
  | Univ, Univ -> true
  | _, _ -> false (* TODO: change to type error *)

and unifyHead (_l: D.lvl) (h1: D.head) (h2: D.head): bool =
  match h1, h2 with
  | Local a, Local b -> a == b

and unifySpine l elims elims2 =
  match elims, elims2 with
  | [], [] -> true
  | x :: xs, y :: ys ->
    unifyElim l x y
    && unifySpine l xs ys
  | _, _ -> false (* TODO: change to a type error thingy *)

and unifyElim l x y =
  match x, y with
  | Ap a, Ap b -> unify l a b
  | First, First -> true
  | Second, Second -> true
  | _, _ -> false (* TODO: change to a type error *)

let rec check (ctx: ctx) (syn: S.syn) (typ: D.dom): S.syn =
  match syn, typ with
  | S.Lam (nm, body), D.Pi (nm', head, clo) ->
    let body' = check (bind ctx nm' head) body (E.inst_clo clo (new_var ctx)) in
    S.Lam (nm, body')
  | S.Pair (a, b), D.Sg (_nm, head, clo) ->
    let atyp = check ctx a head in
    let body' = check ctx b (E.inst_clo clo (new_var ctx)) in
    S.Pair (atyp, body')
  | S.Let (nm, typ, equals, body), t ->
    let typ' = check ctx typ D.Univ in
    let vtyp = E.eval (ctx.terms) typ' in
    let equals' = check ctx equals vtyp in
    let vequals = E.eval (ctx.terms) equals' in
    let body' = check (define ctx nm vequals vtyp) body t in
    S.Let (nm, typ', equals', body')
  | s, t ->
    let typ = infer ctx s in
    if not @@ unify ctx.lvl (snd typ) t then begin
      D.pp (snd typ);
      D.pp t;
      print_endline "oopsy! type error :(";
      H.cannot "bad :("
    end 
    else 
      fst typ

and infer (ctx: ctx) (syn: S.syn): (S.syn * D.dom) =
  match syn with
  | S.Local ix -> S.Local ix, D.index ctx.types ix
  | S.Let (nm, typ, head, body) ->
    let typ' = check ctx typ D.Univ in
    let vtyp = E.eval ctx.terms typ' in
    let head' = check ctx head vtyp in
    let body = infer ctx body in
    S.Let(nm, typ', head', fst body), snd body
  | S.Lam (_, _) -> H.sorry "can't infer lams yet"
  | S.Ap (a, b) ->
    let atyp = infer ctx a in
    begin match snd atyp with
      | D.Pi (_nm, head, clo) ->
        let b' = check ctx b head in
        (S.Ap (fst atyp, b')), (inst_newvar ctx.lvl clo)
      | _ -> H.sorry "can't apply to non-pi"
    end 
  | S.Pair (a, b) ->
    (* test this *)
    let atyp = infer ctx a in
    let btyp = infer ctx b in
    S.Pair (fst atyp, fst btyp), D.Sg ("_", snd atyp, {tm = fst btyp; env = ctx.terms})
  | S.First f ->
    let ftyp = infer ctx f in
    begin match snd ftyp with
      | D.Sg (_, head, _) -> S.First f, head
      | _ -> H.cannot "can't first non-sigma"
    end 
  | S.Second f ->
    let ftyp = infer ctx f in
    begin match snd ftyp with
      | D.Sg (_, _, clo) -> S.Second f, inst_newvar ctx.lvl clo
      | _ -> H.cannot "can't second non-sigma"
    end
  | S.Pi (nm, head, clo) ->
    let head' = check ctx head D.Univ in
    let vhead = E.eval ctx.terms head in
    let clo' = check (bind ctx nm vhead) clo D.Univ in
    S.Pi (nm, head', clo'), Univ
  | S.Sg (nm, head, clo) ->
    let head' = check ctx head D.Univ in
    let vhead = E.eval ctx.terms head in
    let clo' = check (bind ctx nm vhead) clo D.Univ in
    S.Sg (nm, head', clo'), Univ
  | S.Univ -> S.Univ, D.Univ
