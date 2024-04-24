module S = Syntax
open S.Constructors

let (@@) f x = f x
let fst' (a, _) = a
let snd' (_, b) = b

let meta m = S.Meta (Metas.Metaid m)

let l x = local x

let bool' x =
  let_ "Bool"
    u
    (pi "B" (meta 0) (pi "_" (l 0) (pi "_" (l 1) (l 2))))
  @@ 
  let_ "true"
    (l 0)
    (lam "B" (lam "t" (lam "f" (l 1))))
  @@
  let_ "false"
    (l 1)
    (lam "B" (lam "t" (lam "f" (l 0))))
  @@
  let_ "not"
    (pi "_" (l 2) (l 3))
    (lam "b" (lam "B" (lam "t" (lam "f"
                                  (ap (ap (ap (l 3) (l 2)) (l 0)) (l 1))
                               ))))
    x

let eq' x =
  let_ "Eq"
    (pi "A" u (pi "_" (l 0) (pi "_" (l 1) u)))
    (lam "A"
       (lam "x"
          (lam "y"
             (pi "P" (pi "_" (l 2) u)
                (pi "_" (ap (l 0) (l 2)) (ap (l 1) (l 2)))
             ))))
  @@
  let_ "refl"
    (pi "A" u (pi "x" (l 0) (ap (ap (ap (l 2) (l 1)) (l 0)) (l 0))))
    (lam "A" (lam "x" (lam "P" (lam "px" (l 0)))))
  @@
  x
