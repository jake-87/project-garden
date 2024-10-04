type ml =
  | V of string
  | U
  | App of ml * ml
  | Pair of ml * ml
  | In of int * ml
  | Pr of int * ml
  | Fn of string * ml
  | Let of string * ml * ml
  | Case of ml * string * ml * string * ml
[@@deriving show {with_path = false}]

type ctm =
  | Cletv of string * cval * ctm
  | Clet of string * int * string * ctm
  | Cletc of string * string * ctm * ctm
  | Cappc of string * string
  | Capp of string * string * string
  | Ccase of string * string * string
[@@deriving show {with_path = false}]

and cval =
  | CU
  | Cpair of string * string
  | Cin of int * string
  | Cfn of string * string * ctm
[@@deriving show {with_path = false}]

let rec spaces i =
  if i = 0 then ""
  else " " ^ (spaces (i - 1))

let (let@) x f = x f

let rec p_ctm i ctm =
  print_string (spaces i);
  match ctm with
  | Clet(a,i,b,e) -> print_string ("let " ^ a ^ " = p" ^ string_of_int i
                                   ^ " " ^ b ^ " in\n");
                    p_ctm (i+2) e
  | Cletv(a,v,e) -> print_string ("letv " ^ a ^ " = "); p_cval (i+1)v;
                   print_string" in\n";
                   p_ctm (i+1) e
  | Cletc(a,b,e1,e2) ->
     print_string ("letc " ^ a ^ " " ^ b ^ " =\n"); p_ctm (i+1)e1;
     print_string " in\n";
     p_ctm (i) e2
  | Cappc(a,b) -> print_string @@ a ^ " " ^ b
  | Capp(a,b,c) -> print_string @@ a ^ " " ^ b ^ " " ^ c
  | Ccase(a,b,c) -> print_string @@ "case " ^ a ^ " of |l=> " ^ b ^ " |r=> " ^ c 
and p_cval i cval =
  match cval with
  | CU -> print_string "()"
  | Cpair(a,b) -> print_string ("(" ^ a ^ ", " ^ b ^ ")")
  | Cin(i,s) -> print_string @@ "inj" ^ string_of_int i ^ " " ^ s
  | Cfn(a,b,e) -> print_string @@ "funk " ^ a ^ " " ^ b ^ " ->\n";
                 p_ctm i e
  

let fv =
  let s = ref 0 in
  fun () -> let t = !s in incr s; "v" ^ string_of_int t

let fk =
  let s = ref 0 in
  fun () -> let t = !s in incr s; "k" ^ string_of_int t


let rec sq ml k =
  match ml with
  | V s -> k s
  | U -> let x=fv() in Cletv(x, CU, k x)
  | App(e1,e2) ->
     let@ z1 = sq e1 in
     let@ z2 = sq e2 in 
     let x = fv() in
     let c = fk() in 
     Cletc(c, x, k x, Capp(z1,c,z2))
  | Pair(a,b) ->
     let@ z1 = sq a in
     let@ z2 = sq b in
     let x=fv()in 
     Cletv(x, Cpair(z1,z2), k x)
  | In(i, e) ->
     let@ z = sq e in
     let x=fv()in 
     Cletv(x, Cin(i, z), k x)
  | Pr(i, e) ->
     let@ z = sq e in 
     let x=fv()in 
     Clet(x, i, z, k x)
  | Fn(x, e) ->
     let f=fv() in
     let c=fk()in 
     Cletv(f, Cfn(c,x,rd e c), k f)
  | Let(x,e1,e2) ->
     let j=fv()in
     Cletc(j,x,sq e2 k, rd e1 j)
  | Case(e,x1,e1,x2,e2) ->
     let@ z = sq e in
     let j=fk()in
     let k1=fk()in
     let k2=fk()in
     let x=fv()in 
     Cletc(j, x, k x,
           Cletc(k1,x1,rd e1 j,
                 Cletc(k2,x2,rd e2 j,
                       Ccase(z,k1,k2)
                   )
             )
       )

and rd ml k =
  match ml with
  | V s -> Cappc(k, s)
  | App(e1,e2) ->
     let@ x1 = sq e1 in
     let@ x2 = sq e2 in
     Capp(x1,k,x2)
  | Fn(x,e) ->
     let f=fv()in
     let j=fk()in
     Cletv(f, Cfn(j,x,rd e j),Cappc(k, f))
  | Pair(e1,e2) ->
     let@ x1 = sq e1 in
     let@ x2 = sq e2 in
     let x=fv()in
     Cletv(x,Cpair(x1,x2),Cappc(k,x))
  | In(i, e) ->
     let@ z = sq e in
     let x=fv()in
     Cletv(x,Cin(i,z),Cappc(k,z))
  | U ->
     let x=fv()in
     Cletv(x, CU, Cappc(k,x))
  | Pr(i, e) ->
     let@ z = sq e in
     let x=fv()in 
     Clet(x,i,z,Cappc(k,x))
  | Let(x,e1,e2) ->
     let j = fk()in 
     Cletc(j,x,rd e2 k, rd e1 j)
  | Case(e,x1,e1,x2,e2) ->
     let@ z = sq e in
     let k1,k2=fk(),fk()in 
     Cletc(k1,x1,rd e1 k,
           Cletc(k2,x2,rd e2 k,
                 Ccase(z,k1,k2)
             )
       )

let () =
  let example =
    Let("pair", Fn("x",Fn("y",Pair(V"x",V"y"))),
        Let("swap", Fn("arg", Case(V"arg","a",In(1,V"a"),"b",In(0,V"b"))),
            App(V"swap",App(V"pair",App(V"q",V"w")))
          )
      )
  in
  print_endline "start:";
  print_endline (show_ml example);
  let as_cps = rd example "NEXT" in
  print_endline "\nafter:";
  print_endline (show_ctm as_cps);
  print_endline "\nslash\n";
  p_ctm 0 as_cps;
