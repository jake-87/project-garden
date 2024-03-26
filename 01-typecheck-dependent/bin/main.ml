

let () =
  let t = Tests.unif_test in
  print_endline "raw:";
  Raw.print [] t;
  print_newline ();
  print_endline "typechecking...";
  let tm, ty = Bidir.infer' t in
  print_endline "\nresult:";
  Domain.print ty;
  Raw.print [] tm;
  print_endline "\n\nfrom:";
  Raw.print [] t;
  print_newline ();
  print_endline "done"
