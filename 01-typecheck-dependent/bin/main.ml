open Raw
module D = Domain
open Quote
open Eval

let () =
  let t = Let("id",
              None,
              Lam("a", None, Local 0),
              Let("x",
                  None,
                  Local 0,
                  App(Local 1, Local 0)
                 )
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
  print_endline "done"
