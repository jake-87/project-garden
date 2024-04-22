module S = Syntax
module D = Domain
module E = Eval
module Q = Quote
module H = Helpers
module B = Bidir

open S.Constructors

let (@@) f x = f x

let example : S.syn =
  lam "x" (pair (local 0) (local 0))

let exampletyp : D.dom =
  D.Pi ("_", Univ, {tm = sg "n" Univ Univ; env = [] })

let main () =
  let typ = B.check (B.empty_ctx ()) example exampletyp in
  S.pp [] typ
    
