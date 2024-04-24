module S = Syntax
module D = Domain
module E = Eval
module Q = Quote
module H = Helpers
module B = Bidir

open S.Constructors

let (@@) f x = f x
let fst' (a, _) = a
let snd' (_, b) = b

let meta m = S.Meta (Metas.Metaid m)

let l x = local x
module Ex = Examples

let example : S.syn =
  Ex.bool'
  @@
  Ex.eq'
  @@
  let_ "eqtest"
    (ap (ap (ap (l 1) (meta 1)) (l 3)) (ap (l 2) (ap (l 2) (l 3))))
    (ap (ap (l 0) (meta 2)) (meta 3))
  @@
  u
  
let typ : S.syn =
  u

let typ' : D.dom = E.eval [] typ

let main () =
  let m i = Metas.Metaid i in
  let ctx = B.ctx_with_metas [m 0; m 1; m 2; m 3; m 4; m 5] in
  print_endline "value:";
  S.pp [] example;
  print_endline "\ntype (raw):";
  S.pp [] typ;
  print_endline "\ntype:";
  D.pp typ';

  print_string "\npress enter to continue: ";
  ignore (read_line ());

  print_endline "\nbidir:";
  let ret = B.check ctx example typ' in
  print_newline ();
  S.pp [] ret;
  print_endline "\nmetas:";
  Metas.pp_metamap D.pp_solver Format.std_formatter ctx.metactx 
