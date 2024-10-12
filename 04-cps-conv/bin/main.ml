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

type ctm =
  | Cletv of string * cval * ctm
  | Clet of string * int * string * ctm
  | Cletc of string * string * ctm * ctm
  | Cappc of string * string
  | Capp of string * string * string
  | Ccase of string * string * string

and cval =
  | CU
  | Cpair of string * string
  | Cin of int * string
  | Cfn of string * string * ctm

let rec spaces i =
  if i = 0 then ""
  else "  " ^ (spaces (i - 1))

let (let@) x f = x f

let rec p_ctm i ctm =
  print_string (spaces i);
  match ctm with
  | Clet(a,i,b,e) -> print_string ("let " ^ a ^ " = p" ^ string_of_int i
                                   ^ " " ^ b ^ " in\n");
                    p_ctm (i) e
  | Cletv(a,v,e) -> print_string ("letv " ^ a ^ " = "); p_cval (i+1)v;
                   print_string" in\n";
                   p_ctm (i) e
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

let fj =
  let s = ref 0 in
  fun () -> let t = !s in incr s; "j" ^ string_of_int t

let rec sq tm k =
    match tm with
    | V x -> k x
    | U -> let x=fv()in Cletv(x,CU,k x)
    | App(a,b) ->
        let@ z1 = sq a in
        let@ z2 = sq b in
        let k'=fk() in
        let x=fv() in
        Cletc(k',x,k x,Capp(z1,k',z2)) 
    | Pair(a,b) ->
        let@ z1 = sq a in
        let@ z2 = sq b in
        let x=fv() in
        Cletv(x,Cpair(z1,z2),k x)
    | In(i,a) ->
        let@ z = sq a in
        let x=fv() in
        Cletv(x, Cin(i,z), k x)
    | Pr(i, a) -> 
        let@ z = sq a in
        let x=fv() in
        Clet(x,i,z,k x)
    | Fn(a,e) ->
        let f=fk()in
        let k'=fk()in
        let x=fv()in
        Cletv(k', Cfn(k',x,rd e k'), k f)
    | Let(a,e1,e2) ->
        let j=fj()in
        let x=fv()in
        Cletc(j,x,sq e2 k,rd e1 j)
    | Case(e,a,e1,b,e2) ->
        let@ z = sq e in
        let k1,k2,x1,x2 = fk(),fk(),fv(),fv() in 
        let j, x = fj(),fv() in
        Cletc(j,x,k x,
        Cletc(k1,x1,rd e1 j,
        Cletc(k2,x2,rd e2 j,
        Ccase(z,k1,k2)
        )
        ))
and rd tm k = 
    match tm with
    | V x -> Cappc(k, x)
    | U -> let x=fv()in Cletv(x,CU,Cappc(k, x))
    | App(a,b) -> 
        let@ x1 = sq a in
        let@ x2 = sq b in
        Capp(x1,k,x2)
    | Fn(x,e) ->
        let f,j=fk(),fj()in
        Cletv(f,Cfn(j,x,rd e j), Cappc(k,f))
    | Pair(a,b) ->
        let@ z1 = sq a in
        let@ z2 = sq b in
        let x = fv()in
        Cletv(x, Cpair(z1,z2), Cappc(k,x))
    | In(i,a) -> 
        let@ z = sq a in
        let x=fv() in
        Cletv(x,Cin(i,z),Cappc(k,x))
    | Pr(i,a) ->    
        let@ z = sq a in
        let x=fv()in
        Clet(x,i,z,Cappc(k,x))
    | Let(x,e1,e2) ->
        let j=fj()in
        Cletc(j,x,rd e2 k,rd e1 j)
    | Case(e,a,e1,b,e2) ->
        let@ z = sq e in
        let k1,k2,x1,x2 = fk(),fk(),fv(),fv() in
        Cletc(k1,x1,rd e1 k,
        Cletc(k2,x2,rd e2 k,
        Ccase(z,k1,k2)
        )
        )

let () =
  let example =
    Let("pair", Fn("x",Fn("y",Pair(V"x",V"y"))),
        Let("swap", Fn("arg", Case(V"arg","a",In(1,V"a"),"b",In(0,V"b"))),
            Let("arg",In(0,V"a"),
            App(V"swap",V"arg"))
          )
      )
  in
  let as_cps = rd example "NEXT" in
  p_ctm 0 as_cps;
