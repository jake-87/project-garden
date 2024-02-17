let lvl_to_ix size lvl =
  let res = size - lvl - 1 in
  print_string "\nlvl_to_ix sz:";
  print_int size;
  print_string " lvl:";
  print_int lvl;
  print_string " res:";
  print_int res;
  print_newline ();
  res
  
let ix_to_lvl size ix =
  let res = size - ix - 1 in
  print_string "\nix_to_lvl sz:";
  print_int size;
  print_string " ix:";
  print_int ix;
  print_string " res:";
  print_int res;
  print_newline ();
  res
