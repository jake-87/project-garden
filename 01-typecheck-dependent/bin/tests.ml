open Raw
module D = Domain
open Quote
open Eval

open Bidir 

let let_ a b c d = Let(a,b,c,d)
let some x = Some x
let pi a b c = Pi(a, b, c)
let lam a b c = Lam(a,b,c)
let ix a = Local (Ix a)
let app a b = App(a,b)

let refl f =
  let_ "Eq"
    (some @@ pi "A" Univ (pi "_" (ix 0) (pi "_" (ix 1) Univ)))
    (lam "A" None @@
     lam "x" None @@
     lam "y" None @@
     pi "P" (pi "_" (ix 2) Univ)
       (pi "_" (app (ix 0) (ix 2)) (app (ix 1) (ix 2))))
  @@
  let_ "refl"
    (some @@ pi "A" Univ @@ pi "x" (ix 0) @@ app (app (app (ix 2) (ix 1)) (ix 0)) (ix 0))
    (
      lam "A'" None @@
      lam "x'" None @@
      lam "P'" None @@
      lam "px'" None @@
      ix 0
    )
  @@
  f

let refl_test =
  let_ "Eq"
    (some @@ pi "A" Univ (pi "_" (ix 0) (pi "_" (ix 1) Univ)))
    (lam "A" None @@
     lam "x" None @@
     lam "y" None @@
     pi "P" (pi "_" (ix 2) Univ)
       (pi "_" (app (ix 0) (ix 2)) (app (ix 1) (ix 2))))
  @@
  let_ "refl"
    (some @@ pi "A" Univ @@ pi "x" (ix 0) @@ app (app (app (ix 2) (ix 1)) (ix 0)) (ix 0))
    (
      lam "A'" None @@
      lam "x'" None @@
      lam "P'" None @@
      lam "px'" None @@
      ix 0
    )
  @@
  let_ "univ=univ"
    (some @@ app (app (app (ix 1) Univ) Univ) Univ)
    (
      app (app (ix 0) Univ) Univ
    )
    Univ

let unif_test =
  refl
  @@
  let_ "eqTest"
    (some @@ app (app (app (ix 1) (Meta 0)) Univ) Univ)
    (app (app (ix 0) (Meta 1)) (Meta 2))
    Univ
