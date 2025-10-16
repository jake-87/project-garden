# Algorithm J

Does not include a parser. One must modify the file if you want to change the term.

some example outputs:
```hs
-- \x. let y = x in y
term: Lam "x" (Let "y" (Var "x") (Var "y"))
-- a. a -> a
type: Right (Ty'Arr (Ty'Poly "?m0") (Ty'Poly "?m0"))

-- \b x. let f = 
           \y. if b then x else y 
         in
         f
term: Lam "b" (Lam "x" (Let "f" (Lam "y" (ITE (Var "b") (Var "x") (Var "y"))) (Var "f")))
-- a. bool -> a -> (a -> a)
type: Right (Ty'Arr Ty'Bool (Ty'Arr (Ty'Poly "?m0") (Ty'Arr (Ty'Poly "?m0") (Ty'Poly "?m0"))))

-- let fst = 𝜆x y. x in fst (fst (\k. k) fst) (fst fst fst)
term: Let "fst" (Lam "x" (Lam "y" (Var "x"))) (App (App (Var "fst") (App (App (Var "fst") (Lam "k" (Var "k"))) (Var "fst"))) (App (App (Var "fst") (Var "fst")) (Var "fst")))
-- a. a -> a
type: Right (Ty'Arr (Ty'Poly "?m2") (Ty'Poly "?m2"))
```
All of these are correct per ocaml's type inference.
