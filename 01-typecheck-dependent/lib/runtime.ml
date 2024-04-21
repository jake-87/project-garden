module S = Syntax
module D = Domain
module E = Eval
module Q = Quote
module H = Helpers

open S.Constructors

let (@@) f x = f x

let example : S.syn =
  lam "A"
  @@ lam "x"
  @@ lam "y"
  @@ pi "P" (arr (local 2) u)
  @@ arr (ap (local 0) (local 2))
  @@ ap (local 1) (local 2)


let evald = E.eval [] example

let quoted = Q.quote (D.Lvl 0) evald

let main () =
  S.pp [] example;
  D.pp evald;
  S.pp [] quoted
  

  
