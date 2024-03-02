open Debru
module R = Raw 
module D = Domain
module M = Metavar

let mctx : D.t M.metactx = M.new_metactx ()

let fresh_meta () =
  M.fresh_meta mctx (fun x -> R.Meta x)


type partial_rename = {
  dom: D.lvl;
  codom: D.lvl;
  renaming: (int * int) list;
}

let lookup {dom; codom; renaming} i =
  List.assoc i renaming

let add_bound {dom = Lvl dom; codom = Lvl codom; renaming} =
  {dom = Lvl (dom + 1);
   codom = Lvl (codom + 1);
   renaming = (codom, dom) :: renaming }


let spine_to_ren lvl env =
  let rec go sp : (int * (int * int) list)=
    match sp with
    | [] -> (0, [])
    | x :: t ->
      let dom, ren = go t in
      match D.force x with
      | D.Stuck (D.Var (Lvl x)) ->
        if not @@ List.exists (fun q -> fst q = x) ren then
          (dom + 1, (x, dom) :: ren)
        else begin
          print_endline "bad: spine_to_dom failed";
          failwith "see above"
        end
      | _ -> failwith "bad: spine_to_dom not on variable"
  in
  let dom, ren = go env in
  {
    dom = Lvl dom;
    codom = Lvl lvl;
    renaming = ren;
  }

let perform_rename m partial v: R.t =
  let rec goStuck partial stuck =
    match stuck with
    | D.App {fn; arg} ->
      R.App (
        goStuck partial fn,
        go partial arg
      )
    | D.Meta m' ->
      if m' = m then
        failwith "occurs check"
      else
        R.Meta m'
    | D.Var (Lvl l) ->
      if not @@ M.lookup mctx m then
        failwith "variable escaped scope"
      else
        let Lvl d = partial.dom in
        R.Local (Ix (Debru.lvl_to_ix d l))
    | D.Fst x -> R.Proj1 (goStuck partial x)
    | D.Snd x -> R.Proj2 (goStuck partial x)
  and go partial v: R.t =
    match v with
    | D.Stuck t -> goStuck partial t
    | D.Lam (nm, clo) ->
      R.Lam(nm, None,
            go
              (add_bound partial)
              (Eval.inst_clo clo (D.Stuck (D.Var partial.codom))))
    | D.Pi (nm, t, clo) ->
      R.Pi (nm, go partial t, go (add_bound partial)
              (Eval.inst_clo clo (D.Stuck (D.Var partial.codom))))
    | D.Sigma (nm, t, clo) ->
      R.Sigma(nm, go partial t, go (add_bound partial)
                (Eval.inst_clo clo (D.Stuck (D.Var partial.codom))))
    | D.Pair(a, b) ->
      R.Pair(go partial a, go partial b)
    | Univ -> Univ
  in
  go partial v
