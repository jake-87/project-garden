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

let rec p_tm v m =

  match m with
  | V s -> print_string s
  | U -> print_string "U"
  | App(a,b) -> print_string "("; p_tm 0 a; print_string ") ("; p_tm 0 b; print_string ")"
  | Pair(a,b) -> print_string "("; p_tm 0 a; print_string ", "; p_tm 0 b; print_string ")"
  | In(i, m) -> print_string "inj"; print_int i; print_string " ("; p_tm 0 m; print_string ")"
  | Pr(i, m) -> print_string "prj"; print_int i; print_string " ("; p_tm 0 m; print_string ")"
  | Fn (s, m) -> print_string "fun "; print_string s; print_string " -> "; p_tm v m
  | Let(s,a,b) -> print_string "let "; print_string s; print_string " = ";
      p_tm v a; print_string " in\n"; 

      p_tm (v + 1) b
  | Case (c, a, am, b, bm) ->
      print_string "case "; p_tm v c; print_string " of\n";
      for i = 0 to v do begin
        print_string " "
      end done;print_string ("inj0 " ^ a ^ " -> "); p_tm v am; print_newline();
      for i = 0 to v do begin
        print_string " "
      end done;print_string ("inj1 " ^ b ^ " -> "); p_tm v bm; print_newline();


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

let rec count (tm: ctm) s =
  let i x = if x = s then 1 else 0 in
  match tm with
  | Cletv (_, a, b) -> count_v a s + count b s
  | Clet(a,_,q,_) when a = s && q = s -> 1
  | Clet(a,_,_,_) when a = s -> 0
  | Clet (_, _, q, e) -> i q + count e s
  | Cletc(a,k,_,_) when a = s || k = s -> 0
  | Cletc (_, _, a, b) -> count a s + count b s
  | Cappc (a, b) -> i a + i b
  | Capp (a, b, c) -> i a + i b + i c
  | Ccase (a, b, c) -> i a + i b + i c
and count_v v s =
  let i x = if x = s then 1 else 0 in
  match v with
  | CU -> 0
  | Cpair (a, b) -> i a + i b
  | Cin (_, a) -> i a
  | Cfn (a, b, _) when a = s || b = s -> 0
  | Cfn(_,_,e) -> count e s

let rec subst_v tm s1 s2 =
  match tm with
  | Cpair(a,b) when a = b && b = s1 -> Cpair(s2, s2)
  | Cpair(a,b) when a = s1 -> Cpair(s2, b)
  | Cpair(a,b) when b = s1 -> Cpair(a, s2)
  | Cin(i,e) when e = s1 -> Cin(i, s2)
  | Cfn(k,_,_) when k = s1 -> tm
  | Cfn(k,a,e) when a = s1 -> Cfn(k, s2, subst e s1 s2)
  | e -> e

and subst e q w =
  match e with
  | Cletv(s,v,e) when s = q -> Cletv(s,subst_v v q w,e)
  | Cletv(s,v,e) -> Cletv(s,subst_v v q w,subst e q w)
  | Clet(s,i,p,e) when s = q && p = q -> Clet(s,i,w,e)
  | Clet(s,_i,_p,e) when s = q -> e
  | Clet(s,i,p,e) when p = q -> Clet(s,i,w,subst e q w)
  | Clet(s,i,p,e) -> Clet(s,i,p,subst e q w)
  | Cletc(s,b,r,t) when s = q -> Cletc(s,b,subst r q w, t)
  | Cletc(s,p,e1,e2) when p = q -> Cletc(s,w,subst e1 q w,subst e2 q w)
  | Cletc(s,p,e1,e2) -> Cletc(s,p,subst e1 q w,subst e2 q w)
  | Cappc(s,p) when s = q && p = q -> Cappc(w,w)
  | Cappc(s,p) when s = q -> Cappc(w,p)
  | Cappc(s,p) when p = q -> Cappc(s,w)
  | Cappc(s,p) -> Cappc(s,p)
  | Capp(a,b,c) ->
      let sel a = if a = q then w else a in
      let a,b,c = sel a, sel b, sel c in
      Capp(a,b,c)
  | Ccase(a,b,c) ->
      let sel a = if a = q then w else a in
      let a,b,c = sel a, sel b, sel c in
      Ccase(a,b,c)


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
  | Fn(x,e) ->
      let f=fk()in
      let k'=fk()in

      Cletv(k', Cfn(k',x,rd e k'), k f)
  | Let(x,e1,e2) ->
      let j=fj()in

      Cletc(j,x,sq e2 k,rd e1 j)
  | Case(e,x1,e1,x2,e2) ->
      let@ z = sq e in
      let k1,k2 = fk(),fk() in 
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
  | Case(e,x1,e1,x2,e2) ->
      let@ z = sq e in
      let k1,k2 = fk(),fk() in
      Cletc(k1,x1,rd e1 k,
            Cletc(k2,x2,rd e2 k,
                  Ccase(z,k1,k2)
                 )
           )

let rec hoist tm =
  let f = hoist in
  match tm with
  (* rewrite *)
  | Cletc(a,b,e1,Cletv(q,v,e2)) ->
      Cletv(q,v,Cletc(a,b,e1,e2))
  (* inline *)
  | Cletc(a,b,Cappc(q,w),e) when b = w ->
      subst e a q
  (* inline *)
  | Cletc(a,b,body,Cappc(q,w)) when q = a ->
      Cletc(a,b,body,subst body b w)

  (* dead value elim *)
  | Cletc(a,_,_,e1) when count e1 a = 0 -> e1
  | Clet(a,_,_,e1) when count e1 a = 0 -> e1
  | Cletv(a,_,e1) when count e1 a = 0 -> e1

  (* propogate *)
  | Cletc(a,b,e1,e2) -> Cletc(a,b,f e1,f e2)
  | Clet(a,i,b,e) -> Clet(a,i,b,f e)
  | Cletv(a,v,e) -> Cletv(a,hoist_v v,f e)
  | t -> t

and hoist_v (tm: cval) =
  match tm with
  | Cfn (a, b, e) -> Cfn(a,b,hoist e)
  | _ -> tm

let rec fixish tm =
  let n = hoist tm in
  if n = tm then n
  else fixish n 

let () =
  let example =
    Let("getone", Fn("arg", Case(V"arg","a",V"a","b",V"b")),
        Let("arg",In(0,In(0,V"a")),
            App(V"getone",App(V"getone",V"arg")))
       )
  in
  p_tm 0 example;
  print_endline "\n\n";
  let as_cps = rd example "NEXT" in
  p_ctm 0 as_cps;
  print_endline "\n\nhoist:\n\n";
  let h = fixish as_cps in
  print_endline "\n\n";
  p_ctm 0 h
