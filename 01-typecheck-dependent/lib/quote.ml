module S = Syntax
module D = Domain
module E = Eval 
module H = Helpers
open S.Constructors

(* quote from the domain to the syntax
   general structure is undoing closures by instantiating with variables
   and taking stuck terms back to their "proper" representation in
   syntax land
*)

let rec quote (l: D.lvl) (tm: D.dom): S.syn =
  match tm with
  | D.Pair (a, b) -> pair (quote l a) (quote l b) 
  | D.Lam (nm, clo) ->
    lam nm (quote (D.lvlsucc l) (E.inst_clo clo (Stuck {tm = Local l; elims=[]})))
  | D.Pi (nm, a, clo) ->
    pi nm (quote l a) (quote (D.lvlsucc l) (E.inst_clo clo (Stuck {tm=Local l; elims=[]})))
  | D.Sg (nm, a, clo) ->
    sg nm (quote l a) (quote (D.lvlsucc l) (E.inst_clo clo (Stuck {tm=Local l; elims=[]})))
  | D.Stuck s ->
    begin
      let tm' = quoteHead l s.tm in 
      let rec go (e: D.elim list) =
        match e with
        | [] -> tm'
        | x :: xs ->
          let rest = go xs in
          (match x with
           | D.Ap d -> ap rest (quote l d)
           | D.First -> fst rest
           | D.Second -> snd rest
          )
      in
      go s.elims
    end 
  | D.Univ -> S.Univ


and quoteHead (l: D.lvl) (h: D.head): S.syn =
  (match h with
   | D.Local x -> S.Local (Debru.lvl2ix l x)
  )
