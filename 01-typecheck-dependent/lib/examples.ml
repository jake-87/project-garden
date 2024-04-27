module R = Raw
module S = Syntax
open R.Cons


let (@@) f x = f x
let fst' (a, _) = a
let snd' (_, b) = b

let meta m = S.Meta (Metas.Metaid m)

let bool' x =
  let_ "Bool"
    u
    (pi "B" u (arr (l "B") (arr (l "B") (l "B"))))
  @@ 
  let_ "true"
    (l "Bool")
    (lam "B" (lam "t" (lam "f" (l "t"))))
  @@
  let_ "false"
    (l "Bool")
    (lam "B" (lam "t" (lam "f" (l "f"))))
  @@
  let_ "not"
    (arr (l "Bool") (l "Bool"))
    (lam "b"
       (lam "B"
          (lam "t"
             (lam "f"
                (ap4 (l "b") (l "B") (l "f") (l "t"))
             ))))
    x

let eq' x =
  let_ "Eq"
    (ipi "A" u (arr (l "A") (arr (l "A") u)))
    (ilam "A"
       (lam "x"
          (lam "y"
             (pi "P" (arr (l "A") u)
                (arr (ap2 (l "P") (l "x")) (ap2 (l "P") (l "y")))
             ))))
  @@
  let_ "refl"
    (ipi "A" u
       (ipi "x" (l "A")
          (ap3 (l "Eq")(l "x") (l "x"))))
    (ilam "A" (ilam "x" (lam "P" (lam "px" (l "px")))))
  @@
  x

let nat x =
  let_ "Nat"
    u
    (pi "N" u (arr (arr (l "N") (l "N")) (arr (l "N") (l "N"))))
  @@
  let_ "1"
    (l "Nat")
    (lam "N" (lam "s" (lam "z" (ap2 (l "s") (l "z")))))
  @@
  let_ "5"
    (l "Nat")
    (lam "N"
       (lam "s"
          (lam "z"
             (ap2 (l "s") (ap2 (l "s") (ap2 (l "s") (ap2 (l "s") (ap "s" "z")))))
          )))
  @@
  let_ "add"
    (arr (l "Nat") (arr (l "Nat") (l "Nat")))
    (lam "a"
       (lam "b"
          (lam "N"
             (lam "s"
                (lam "z"
                   (ap4 (l "a") (l "N") (l "s")
                      (ap4 (l "b") (l "N") (l "s") (l "z"))))))))
  @@
  let_ "mul"
    (arr (l "Nat") (arr (l "Nat") (l "Nat")))
    (lam "a"
       (lam "b"
          (lam "N"
             (lam "s"
                (lam "z" @@
                   ap4 (l "a") (l "N") (ap3 (l "b") (l "N") (l "s")) (l "z")
                )))))
  @@
  let_ "2"
    (l "Nat")
    (ap3 (l "add") (l "1") (l "1"))
  @@
  let_ "3"
    (l "Nat")
    (ap3 (l "add") (l "2") (l "1"))
  @@    
  x
