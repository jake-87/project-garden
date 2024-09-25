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
     sq e1 (fun z1 ->
         sq e2 (fun z2 ->
             let x = fv() in
             let c = fk() in 
             Cletc(c, x, k x, Capp(z1,c,z2))
           )
       )
  | Pair(a,b) ->
     sq a (fun z1 ->
         sq b (fun z2 ->
             let x=fv()in 
             Cletv(x, Cpair(z1,z2), k x)
           )
       )
  | In(i, e) -> sq e (fun z ->
                                let x=fv()in 

                   Cletv(x, Cin(i, z), k x)
                 )
  | Pr(i, e) -> sq e (fun z ->
                                let x=fv()in 

                   Clet(x, i, z, k x)
                 )
  | Fn(x, e) -> let f=fv() in
               let c=fk()in 

               Cletv(f, Cfn(c,x,rd e c), k f)
  | Let(x,e1,e2) ->
     let j=fv()in
     Cletc(j,x,sq e2 k, rd e1 j)
  | Case(e,x1,e1,x2,e2) ->
     sq e (fun z ->
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
       )
and rd ml k =
  match ml with
  | V s -> Cappc(k, s)
  | App(e1,e2) ->
     sq e1 (fun x1 ->
         sq e2 (fun x2 ->
             Capp(x1,k,x2)
           )
       )
  | Fn(x,e) ->
     let f=fv()in
     let j=fk()in
     Cletv(f, Cfn(j,x,rd e j),Cappc(k, f))
  | Pair(e1,e2) ->
     sq e1 (fun x1 ->
         sq e2 (fun x2 ->
             let x=fv()in
             Cletv(x,Cpair(x1,x2),Cappc(k,x))
           )
       )
  | In(i, e) -> sq e (fun z -> let x=fv()in Cletv(x,Cin(i,z),Cappc(k,z)))
  | U -> let x=fv()in Cletv(x, CU, Cappc(k,x))
  | Pr(i, e) -> sq e (fun z ->
                   let x=fv()in 
                   Clet(x,i,z,Cappc(k,x))
                 )
  | Let(x,e1,e2) ->
     let j = fk()in 
     Cletc(j,x,rd e2 k, rd e1 j)
  | Case(e,x1,e1,x2,e2) ->
     sq e (fun z ->
         let k1,k2=fk(),fk()in 
         Cletc(k1,x1,rd e1 k,
               Cletc(k2,x2,rd e2 k,
                     Ccase(z,k1,k2)
                 )
           )
       )


let () =
  (* #1 ((\x -> (g x, x)) y)*)
  let example = Pr(1,(App(Fn("x",Pair(App(V"g",V"x"),V"x")),V"y"))) in
  print_endline "start:";
  print_endline (show_ml example);
  let as_cps = rd example "DONE" in
  print_endline "\nafter:";
  print_endline (show_ctm as_cps)
