open Raw
module D = Domain
open Quote
open Eval

open Bidir 

let () =
  let t = Let(
      "Eq",
      Some (Pi("A", Univ, Pi("_", Local 0, Pi("_", Local 1, Univ)))),
      Lam("A", None,
          Lam("x", Some (Local 0),
              Lam("y", Some (Local 1),
                  Pi("P",
                     Pi("_", Local 2, Univ),
                     Pi("_",
                        App (Local 0, Local 2),
                        App (Local 1, Local 2)
                       ))))),
      Univ
    )
  in
  print_endline "raw:";
  Raw.print [] t;
  print_newline ();
  
  let ev = eval D.empty t in
  print_endline "eval'd:";
  Domain.print ev;
  print_newline ();
  
  let nf = quote 0 ev in
  print_endline "quote'd:";
  Raw.print [] nf;
  print_newline ();

  print_endline "typechecking...";

  let ty = Bidir.infer (Bidir.empty ()) t in
  print_endline "result:";
  Raw.print [] ty;
  
  print_endline "done"
