module D = Domain
module S = Syntax 
module E = Eval
module Q = Quote
module M = Metas
module H = Helpers

type partial_ren = {
  domsize: D.lvl;
  codomsize: D.lvl;
  renaming: (int * D.lvl) list;
}

let lift_new_var (pren: partial_ren): partial_ren =
  {
    domsize = D.lvlsucc pren.domsize;
    codomsize = D.lvlsucc pren.codomsize;
    renaming = (D.unlvl pren.codomsize, pren.domsize) :: pren.renaming;
  }


let create_partial_ren (l: D.lvl) (mmap: D.solver M.metamap) (elims: D.elim list): partial_ren =
  let rec go (elims: D.elim list): (D.lvl * (int * D.lvl) list) =
    match elims with
    | [] -> (Lvl 0, [])
    | D.Ap d :: xs ->
      let (dom, ren) = go xs in
      begin match Q.force mmap d with
        (* check this *)
        | D.Stuck {tm = D.Local (Lvl l); elims = []} ->
          if not @@ List.mem_assoc l ren then
            (D.lvlsucc dom, (l, dom) :: ren)
          else
            H.cannot "duplicate variable in ren"
        | _ -> H.cannot "can't pren non-var"
      end
    | _ -> H.cannot "can't pren non-ap"
  in
  let (dom, ren) = go elims in
  {
    domsize = dom;
    codomsize = l;
    renaming = ren;
  }

let rename (mmap: D.solver M.metamap) (m: M.meta)
    (pren: partial_ren) (tm: D.dom): S.syn =
  let rec goSp (pren: partial_ren) (tm: S.syn) (e: D.elim list): S.syn =
   match e with
    | [] -> tm
    | (D.Ap d) :: xs ->
      S.Ap ((goSp pren tm xs), (go pren d))
    | D.First :: xs ->
      S.First (goSp pren tm xs)
    | D.Second :: xs ->
      S.Second (goSp pren tm xs)
  and go (pren: partial_ren) (v: D.dom): S.syn =
    match Q.force mmap v with
    | D.Pair (a, b) -> S.Pair((go pren a), (go pren b))
    | D.Lam (x, clo) ->
      S.Lam (x,
             go
               (lift_new_var pren)
               (E.inst_clo clo D.Bound
                  (D.Stuck {tm = Local (pren.codomsize); elims = []})))
    | D.Pi (x, hd, clo) ->
      S.Pi (x,
            go pren hd,
            go (lift_new_var pren)
              (E.inst_clo clo D.Bound
              (D.Stuck {tm = Local pren.codomsize; elims =[]}))
           )
    | D.Sg (x, hd, clo) ->
      S.Sg (x,
            go pren hd,
            go (lift_new_var pren)
              (E.inst_clo clo D.Bound
              (D.Stuck {tm = Local pren.codomsize; elims =[]}))
           )
    | D.Stuck s ->
      (
        match s with
        | { tm=Local l; elims } ->
          begin match List.assoc_opt (D.unlvl l) pren.renaming with
            | None -> H.cannot "variable escaping scope"
            | Some n -> goSp pren (S.Local (Debru.lvl2ix (pren.domsize) n)) elims
          end 
        | { tm=Meta m'; elims } ->
          if m' == m then
            H.cannot "occurs check"
          else
            goSp pren (S.Meta m') elims
      ) 
    | D.Univ -> S.Univ
  in
  go pren tm 


let lams (l: D.lvl) (s: S.syn) =
  let l' = D.unlvl l in
  let rec go (x: int) (t: S.syn) =
    if x == l' then
      t
    else
      S.Lam ("$" ^ string_of_int (x + 1), go (x + 1) t)
  in
  go 0 s

let solve (mmap: D.solver M.metamap)
    (l: D.lvl) (mv: M.meta) (e: D.elim list) (rhs: D.dom): unit =
  print_endline "\nsolver:";
  print_string "lvl: ";
  print_int (D.unlvl l);
  print_newline ();
  print_string "meta: ";
  M.pp_meta Format.std_formatter mv;
  Format.print_flush ();
  print_newline ();
  print_string "rhs: ";
  D.pp rhs;
  print_newline ();
  let pren = create_partial_ren l mmap e in
  let rhs = rename mmap mv pren rhs in
  let solution = E.eval [] (lams pren.domsize rhs) in
  print_endline "solution:";
  D.pp solution;
  Format.print_flush();
  M.set mmap mv (Solved solution)
