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

let meta m = S.Meta (Metas.Metaid m)

module Ex = Examples

let term : R.raw =
  Ex.eq'
  @@
  Ex.nat
  @@
  let_ "eqtest"
    (ap4 (l "Eq") hole (l "5") hole)
    (ap3 (l "refl") hole hole)
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
