module S = Syntax
module D = Domain
module E = Eval
module Q = Quote
module H = Helpers
module B = Bidir
module R = Raw

open R.Cons

let (@@) f x = f x
let (++) f x = f x
let fst' (a, _) = a
let snd' (_, b) = b

module Ex = Examples

let term : R.raw =
  Ex.bool'
  @@
  Ex.nat
  @@
  Ex.eq'
  @@
  letrec "foo"
    (arr (l "Bool") (l "Bool"))
    (lam "a" (ap4 (l "a") (l "Bool") (ap "foo" "false") (l "false")))
  @@
  let_ "eqtest"
    (ap3 (l "Eq") (ap2 (l "foo") (ap "not" "false")) (ap "foo" "false"))
    (l "refl")
  @@
  let_ "test2"
    (ap3 (l "Eq") (l "1") (l "1"))
    (l "refl")
  @@
  u
  
let typ : R.raw =
  u

let main () =
  let ctx = B.empty_ctx () in
  
  let term' = Raw.elab ctx [] term in
  let typ' = Raw.elab ctx [] typ in

  print_endline "\nterm:";
  S.pp [] term';
  print_endline "\ntyp:";
  S.pp [] typ';

  let typ'' = E.eval [] typ' in

  print_endline "\nelab typ:";
  D.pp typ'';

  print_string "\npress enter to continue: ";
  ignore (read_line ());

  print_endline "\nbidir:";
  let ret = B.check ctx term' typ'' in
  print_newline ();
  S.pp [] ret;
  print_endline "\nmetas:";
  Metas.pp_metamap D.pp_solver Format.std_formatter ctx.metactx 
