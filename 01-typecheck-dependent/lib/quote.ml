module S = Syntax
module D = Domain
module E = Eval 
module H = Helpers
module M = Metas
open S.Constructors

(* quote from the domain to the syntax
   general structure is undoing closures by instantiating with variables
   and taking stuck terms back to their "proper" representation in
   syntax land
*)

let app_to (fn: D.dom) (arg: D.dom): D.dom =
  match fn with
  | D.Lam (_nm, clo) -> E.inst_clo clo D.Bound arg
  | D.Stuck s -> D.Stuck (D.add_elim s (D.Ap arg))
  | _ -> H.cannot "can't app to non-lam/stuck"

let rec app_to_many (fn: D.dom) (args: D.dom list): D.dom =
  match args with
  | [] -> fn
  | x :: xs ->
    let fn' = app_to_many fn xs in
    app_to fn' x

let assume_aps (e: D.elim list): D.dom list =
  List.map (fun e ->
      match e with
      | D.Ap d -> d
      | _ -> H.cannot "cannot force meta with elim of non-ap"
    ) e

let rec force (metactx: D.solver M.metamap) (tm: D.dom): D.dom =
  match tm with
  | D.Stuck {tm = Meta m; elims} ->
    begin match M.index metactx m with
      | D.Unsolved -> tm
      | D.Solved dm -> force metactx (app_to_many dm (assume_aps elims))
    end
  | _ -> tm

let rec quote (l: D.lvl) (metactx: 'a M.metamap) (tm: D.dom): S.syn =
  match force metactx tm with
  | D.Pair (a, b) -> pair (quote l metactx a) (quote l metactx b) 
  | D.Lam (nm, clo) ->
    lam nm (quote (D.lvlsucc l) metactx
              (E.inst_clo clo D.Bound (Stuck {tm = Local l; elims=[]})))
  | D.Pi (nm, a, clo) ->
    pi nm (quote l metactx a) (quote (D.lvlsucc l) metactx
                         (E.inst_clo clo D.Bound (Stuck {tm=Local l; elims=[]})))
  | D.Sg (nm, a, clo) ->
    sg nm (quote l metactx a) (quote (D.lvlsucc l) metactx
                         (E.inst_clo clo D.Bound (Stuck {tm=Local l; elims=[]})))
  | D.Stuck s ->
    begin
      let tm' = quoteHead l s.tm in 
      app_elims l metactx tm' s.elims
    end 
  | D.Univ -> S.Univ

and app_elims (l: D.lvl) (metactx: D.solver M.metamap) (tm: S.syn) (e: D.elim list) =
  match e with
  | [] -> tm
  | x :: xs ->
    let rest = app_elims l metactx tm xs in
    (match x with
     | D.Ap d -> ap rest (quote l metactx d)
     | D.First -> fst rest
     | D.Second -> snd rest
    )

and quoteHead (l: D.lvl) (h: D.head): S.syn =
  (match h with
   | D.Local x -> S.Local (Debru.lvl2ix l x)
   | D.Meta m -> S.Meta m
  )

let nf (env: D.env) (m: D.solver M.metamap) (tm: S.syn): S.syn =
  quote (Lvl (List.length env)) m (E.eval env tm)
