module S = Syntax
module D = Domain
module E = Eval
module Q = Quote
module H = Helpers
module M = Metas
module P = Partial

type ctx = {
  (* Ix indexed (ie new stuff at the front) *)
  names: string list;
  terms: D.env;
  types: D.env;
  lvl: D.lvl;
  (* all ctxs that derive from a new one share the same
     metamap
  *)
  metactx: D.solver M.metamap;
}

let rec iter3 f a b c =
  match a, b, c with
  | [], [], [] -> ()
  | x :: xs, y :: ys, z :: zs ->
    f x y z;
    iter3 f xs ys zs
  | _, _, _ -> H.cannot "unequal lengths"

let pprint_ctx ctx =
  print_endline "\n\nctx top:";
  iter3 (fun a b c ->
      let b' = Buffer.create 0 in 
      let f = Format.formatter_of_buffer b' in
      Format.pp_print_string f a;
      Format.pp_print_string f " : ";
      D.pp_dom f (snd b);
      Format.pp_print_string f " = ";
      D.pp_dom f (snd c);
      Format.pp_print_newline f ();
      let c = Buffer.contents b' in
      print_string c;
    ) ctx.names ctx.types ctx.terms;
  M.pp_metamap D.pp_solver Format.std_formatter ctx.metactx;
  Format.print_flush();
  print_endline "end ctx\n"
    
let empty_ctx () = {
  names = [];
  terms = [];
  types = [];
  lvl = D.Lvl 0;
  metactx = M.empty ();
}

let ctx_with_metas ms =
  let empty = empty_ctx () in
  List.iter (fun e -> M.set empty.metactx e D.Unsolved) ms;
  empty
  

let new_var (ctx: ctx) = 
  D.Stuck {tm = D.Local ctx.lvl; elims = []}

let from_lvl (l) =
  D.Stuck {tm = D.Local l; elims = []}

let inst_newvar l a =
  E.inst_clo a D.Bound (D.Stuck {tm = D.Local l; elims = []})

let bind (ctx: ctx) (nm: string) (typ: D.dom) =
  {
    names = nm :: ctx.names;
    terms = D.add ctx.terms D.Bound (new_var ctx);
    types = D.add ctx.types D.Bound typ;
    lvl = D.lvlsucc ctx.lvl;
    metactx = ctx.metactx;
  }

let define (ctx: ctx) (nm: string) (body: D.dom) (typ: D.dom) =
  {
    names = nm :: ctx.names;
    terms = D.add ctx.terms D.Defined body;
    (* i think types should always be bound? not quite sure tbh *)
    types = D.add ctx.types D.Bound typ;
    lvl = D.lvlsucc ctx.lvl;
    metactx = ctx.metactx;
  }



let rec unify (mmap: D.solver M.metamap) (l: D.lvl) (d1: D.dom) (d2: D.dom): bool =
  match Q.force mmap d1, Q.force mmap d2 with
  | Pair (a, b), Pair (x, y) ->
    (unify mmap l a x) && (unify mmap l b y)
  | Lam (_, a, i), Lam(_, b, i') ->
    i = i' &&
    unify mmap (D.lvlsucc l) (inst_newvar l a) (inst_newvar l b)
  | Lam (_, b, i), t
  | t, Lam (_, b, i) ->
    unify mmap (D.lvlsucc l) (Q.app_to t (from_lvl l) i) (E.inst_clo b D.Bound (from_lvl l))
  | Sg (_, a, clo), Sg (_, b, clo2) ->
    unify mmap l a b && unify mmap (D.lvlsucc l) (inst_newvar l clo) (inst_newvar l clo2)

  | Pi (_, i, a, clo), Pi (_, i', b, clo2) ->
    i = i' &&
    unify mmap l a b && unify mmap (D.lvlsucc l) (inst_newvar l clo) (inst_newvar l clo2)
  | Stuck {tm = Meta m; elims}, t
  | t, Stuck {tm = Meta m; elims} ->
    P.solve mmap l m elims t;
    true
  | Stuck {tm; elims}, Stuck {tm=tm2; elims=elims2} ->
    unifyHead l tm tm2
    && unifySpine mmap l elims elims2
  | Univ, Univ -> true
  | _, _ -> false (* TODO: change to type error *)

and unifyHead (_l: D.lvl) (h1: D.head) (h2: D.head): bool =
  match h1, h2 with
  | Local a, Local b -> a == b
  | Meta a, Meta b -> a == b
  | _, _ -> false

and unifySpine mmap l elims elims2 =
  match elims, elims2 with
  | [], [] -> true
  | x :: xs, y :: ys ->
    unifyElim mmap l x y
    && unifySpine mmap l xs ys
  | _, _ -> false (* TODO: change to a type error thingy *)

and unifyElim mmap l x y =
  match x, y with
  | Ap (a, _), Ap (b, _) -> unify mmap l a b
  | First, First -> true
  | Second, Second -> true
  | _, _ -> false (* TODO: change to a type error *)

let rec check (ctx: ctx) (syn: S.syn) (typ: D.dom): S.syn =
  pprint_ctx ctx;
  print_endline "\ncheck:";
  S.pp ctx.names syn;
  print_endline "against:";
  D.pp typ;
  match syn, Q.force ctx.metactx typ with
  | S.Lam (nm, body, i), D.Pi (_nm', i', head, clo) when i = i' ->
    
    let body' = check (bind ctx nm head) body (E.inst_clo clo D.Bound (new_var ctx)) in
    S.Lam (nm, body', i)
      
  | t, D.Pi(nm, S.Impl, head, clo) ->
    S.Lam (nm, check (bind ctx nm head) t (E.inst_clo clo D.Bound (new_var ctx)), S.Impl)
  | S.Pair (a, b), D.Sg (_nm, head, clo) ->
    let atyp = check ctx a head in
    let body' = check ctx b (E.inst_clo clo D.Bound (new_var ctx)) in
    S.Pair (atyp, body')
  | S.Let (nm, typ, equals, body), t ->
    let typ' = check ctx typ D.Univ in
    let vtyp = E.eval (ctx.terms) typ' in
    let equals' = check ctx equals vtyp in
    let vequals = E.eval (ctx.terms) equals' in
    let body' = check (define ctx nm vequals vtyp) body t in
    S.Let (nm, typ', equals', body')

  | S.Letrec (nm, typ, head, body), t ->
    let typsyn = check ctx typ D.Univ in
    let vtyp = E.eval (ctx.terms) typsyn in
    let equalsyn = check
        (define ctx nm (D.Stuck {tm = Local (ctx.lvl); elims = []}) vtyp)
        head
        vtyp
    in
    let equals' = E.eval
        ((D.Defined, D.Stuck {tm = Local (ctx.lvl); elims = []}) :: ctx.terms)
        equalsyn
    in
    let ctx' = define ctx nm equals' vtyp in
    let equals'' = E.eval ctx'.terms equalsyn in
    let ctx'' = define ctx nm equals'' vtyp in
    let body' = check ctx'' body t in
    S.Letrec (nm, typsyn, equalsyn, body')

  | s, t ->
    let typ = insert_impl_apps ctx @@ infer ctx s in
    print_endline "\ninferred:";
    S.pp ctx.names (fst typ);
    print_endline "of type";
    D.pp (snd typ);
    print_endline "unifying against:";
    D.pp t;
    if not @@ unify ctx.metactx ctx.lvl (snd typ) t then begin
      print_endline "\ntype err:";
      print_endline "metas:";
      M.pp_metamap D.pp_solver Format.std_formatter ctx.metactx;
      Format.print_flush();
      print_endline "\ncan't unify:";
      print_endline "expected:";
      S.pp ctx.names s;
      print_endline "of type:";
      D.pp t;
      print_endline "got:";
      S.pp ctx.names (fst typ);
      print_endline "of type:";
      D.pp (snd typ);
      H.cannot "bad :("
    end 
    else 
      fst typ

and infer (ctx: ctx) (syn: S.syn): (S.syn * D.dom) =
  pprint_ctx ctx;
  print_endline "\ninfer:";
  S.pp ctx.names syn;
  match syn with
  | S.Local ix -> S.Local ix, Q.force ctx.metactx @@ snd (D.index ctx.types ix)
  | S.Let (nm, typ, head, body) ->
    let typ' = check ctx typ D.Univ in
    let vtyp = E.eval ctx.terms typ' in
    let head' = check ctx head vtyp in
    let body = infer ctx body in
    S.Let(nm, typ', head', fst body), snd body
  | S.Letrec (nm, typ, head, body) ->

    (* basically copy pasted from Check *)
    
    let typsyn = check ctx typ D.Univ in
    let vtyp = E.eval (ctx.terms) typsyn in
    let equalsyn = check
        (define ctx nm (D.Stuck {tm = Local (ctx.lvl); elims = []}) vtyp)
        head
        vtyp
    in
    let equals' = E.eval
        ((D.Defined, D.Stuck {tm = Local (ctx.lvl); elims = []}) :: ctx.terms)
        equalsyn
    in
    let ctx' = define ctx nm equals' vtyp in
    let equals'' = E.eval ctx'.terms equalsyn in
    let ctx'' = define ctx nm equals'' vtyp in
    let body' = infer ctx'' body in
    S.Letrec (nm, typsyn, equalsyn, fst body'), snd body' 

  | S.Lam (nm, bd, i) ->

    let meta = M.fresh_meta () in
    M.set ctx.metactx meta D.Unsolved; 
    let try' = E.eval ctx.terms (S.Meta meta) in
    let (tm, ty) = insert_impl_apps ctx @@ infer (bind ctx nm try') bd in
    S.Lam(nm, tm, i),
    
    D.Pi(nm, i, try', {tm = Q.quote (D.lvlsucc ctx.lvl) ctx.metactx ty; env = ctx.terms})
  | S.Ap (a, b, i) ->
    let (i', a, atyp) =
      match i with
      | S.Impl ->
        let (q, w) = infer ctx a in
        (S.Impl, q, w)
      | S.Expl ->
        let (a, atyp) = insert_impl_apps_pi ctx (infer ctx a) in
        (S.Expl, a, atyp)
    in
    print_endline "\nap: inferred:";
    let tmp = Q.force ctx.metactx atyp in
    D.pp tmp;
    begin match tmp with
      | D.Pi (_nm, pii, head, clo) ->
        if pii <> i' then
          H.cannot "expl/impl conflict";
        print_endline "\nchecking the second arg of ap:";
        S.pp ctx.names a;
        S.pp ctx.names b;
        print_endline "against:";
        D.pp tmp;
        let b' = check ctx b head in
        (S.Ap (a, b', i')), (E.inst_clo clo D.Bound (E.eval ctx.terms b'))
      | _ -> H.sorry "can't apply to non-pi"
    end 
  | S.Pair (a, b) ->
    (* test this *)
    let atyp = infer ctx a in
    let btyp = infer ctx b in
    S.Pair (fst atyp, fst btyp),
    D.Sg ("_", snd atyp,
          {tm = Q.quote (D.lvlsucc ctx.lvl) ctx.metactx (snd btyp); env = ctx.terms})
  | S.First f ->
    let ftyp = infer ctx f in
    begin match Q.force ctx.metactx @@ snd ftyp with
      | D.Sg (_, head, _) -> S.First f, head
      | _ -> H.cannot "can't first non-sigma"
    end 
  | S.Second f ->
    let ftyp = infer ctx f in
    begin match Q.force ctx.metactx @@ snd ftyp with
      | D.Sg (_, _, clo) -> S.Second f, inst_newvar ctx.lvl clo
      | _ -> H.cannot "can't second non-sigma"
    end
  | S.Pi (nm, i, head, clo) ->
    let head' = check ctx head D.Univ in
    let vhead = E.eval ctx.terms head in
    let clo' = check (bind ctx nm vhead) clo D.Univ in
    S.Pi (nm, i, head', clo'), Univ
  | S.Sg (nm, head, clo) ->
    let head' = check ctx head D.Univ in
    let vhead = E.eval ctx.terms head in
    let clo' = check (bind ctx nm vhead) clo D.Univ in
    S.Sg (nm, head', clo'), Univ
  | S.Meta m ->
    begin match M.index ctx.metactx m with
      | Unsolved ->
        let new' = M.fresh_meta () in
        M.set ctx.metactx new' D.Unsolved;
        (S.Meta m, D.Stuck {tm = Meta new'; elims = []})
      | Solved d -> (S.Meta m, d)
    end 
    
  | S.Univ -> S.Univ, D.Univ

and insert_impl_apps_pi ctx (tm, typ) =
  let rec go tm typ =
    match Q.force ctx.metactx typ with
    | D.Pi (_nm, S.Impl, _a, b) ->
      let m = M.fresh_meta () in
      M.set ctx.metactx m Unsolved;
      let m' = S.Meta m in
      let mv = E.eval (ctx.terms) m' in
      go (S.Ap (tm, m', S.Impl)) (E.inst_clo b D.Bound mv)
    | vt -> tm, vt
  in
  go tm typ

and insert_impl_apps ctx (tm, typ) =
  match tm with
  | S.Lam (_, _, S.Impl) -> (tm, typ)
  | _ -> insert_impl_apps_pi ctx (tm, typ)
