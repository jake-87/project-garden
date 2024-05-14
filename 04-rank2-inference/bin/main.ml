type lc =
    | V of string
    | A of lc * lc
    | L of string * lc

let rec p_lc = function
    | V s -> print_string s
    | A (a, b) -> print_string "("; p_lc a; print_string ") ("; p_lc b; print_string ")"
    | L (nm, xs) -> print_string "\\";
        print_string nm;
        print_string ". ";
        p_lc xs

type llc =
    | V' of string
    | A' of llc * llc
    | L1 of string * llc
    | L2 of string * llc
    | L3 of string * llc

let rec subst tm nm t' =
    match tm with
    | V' s when s = nm -> t'
    | A'(a,b) -> A'(subst a nm t', subst b nm t')
    | L1(x, xs) -> if x = nm then tm else L1(x, subst xs nm t')
    | L2(x, xs) -> if x = nm then tm else L2(x, subst xs nm t')
    | L3(x, xs) -> if x = nm then tm else L3(x, subst xs nm t')


let rec p_llc = function
    | V' s -> print_string s
    | A' (a, b) -> print_string "("; p_llc a; print_string ") ("; p_llc b;
        print_string ")"
    | L1 (x, xs) -> print_string "\\1";
        print_string x;
        print_string ". ";
        p_llc xs
    | L2(x, xs) -> print_string "\\2";
        print_string x;
        print_string ". ";
        p_llc xs
    | L3(x ,xs) -> print_string "\\3";
        print_string x;
        print_string ". ";
        p_llc xs

let lami i nm lc =
    if i == 1 then
        L1(nm,lc)
    else if i == 2 then
        L2(nm, lc)
    else if i == 3 then
        L3(nm, lc)
    else
        raise (Failure "oops")

let rec act = function
    | V _ -> []
    | L (x, xs) -> x :: act xs
    | A (a, b) -> match act a with
        | [] -> []
        | x :: xs -> xs

let rec lbl tm ac i =
    match tm with
    | V s -> V' s
    | A (a, b) -> A' (lbl a ac i, lbl b (act b) 3)
    | L (x, xs) -> 
        if List.mem x ac then
            lami i x (lbl xs ac i)
        else
            L1(x, lbl xs ac i)

let nf tm = lbl tm (act tm) 2

let did = ref false

let t () = did := true
let f () = did := false
let m () = !did = true

let fresh =
    let i = ref 0 in
    fun () ->
        incr i;
        string_of_int (!i)

let rec theta1 = function
    | A'(A'(L1(nm, n), p), q) -> t (); A'(L1(nm, A'(n,q)), p)
    | L1(nm, x) -> L1(nm, theta1 x)
    | L2(nm, x) -> L2(nm, theta1 x)
    | L3(nm, x) -> L3(nm, theta1 x)
    | A'(a,b) -> A'(theta1 a, theta1 b)
    | V' s -> V' s

let rec theta2 = function
    | L3(z, A'(L1(y, n), p)) ->
    t ();
    let v = fresh () in
    let w = fresh () in
    let v' = A'(V' v, V' z) in
    let n' = subst n y v' in
    let p' = subst p z (V' w) in
    A'(L1(v, L3(z, n')), L3(w, p'))
    | L1(nm, x) -> L1(nm, theta2 x)
    | L2(nm, x) -> L2(nm, theta2 x)
    | L3(nm, x) -> L3(nm, theta2 x)
    | A'(a,b) -> A'(theta2 a, theta2 b)
    | V' s -> V' s

let rec theta3 = function
    | A'(n, A'(L1(y, p), q)) -> t (); A'(L1(y, A'(n, p)), q)
    | L1(nm, x) -> L1(nm, theta3 x)
    | L2(nm, x) -> L2(nm, theta3 x)
    | L3(nm, x) -> L3(nm, theta3 x)
    | A'(a,b) -> A'(theta3 a, theta3 b)
    | V' s -> V' s

let rec theta4 = function
    | A'(L1(y, L3(x, n)), p) -> t(); L2(x, A'(L1(y, n), p))
    | L1(nm, x) -> L1(nm, theta4 x)
    | L2(nm, x) -> L2(nm, theta4 x)
    | L3(nm, x) -> L3(nm, theta4 x)
    | A'(a,b) -> A'(theta4 a, theta4 b)
    | V' s -> V' s

let rec app_theta tm =
    f ();
    let t' = theta1 (theta2 (theta3 (theta4 tm))) in
    if m () then
    begin
        f ();
        app_theta t' end
    else
    begin
        f ();
        t'
        end

let tbl = Hashtbl.create 100
let gen_of tm =
    let s = match Hashtbl.find_opt tbl tm with
    | Some n -> n
    | None ->
        Hashtbl.add tbl tm (fresh ());
        Hashtbl.find tbl tm
    in
    "delta_" ^ s

let rec gen_cons bound tm =
    ("", gen_of tm) ::
    match tm with
    | V' s -> if List.mem s bound then [] else [s, "beta_" ^ s]
    | A' (a, b) -> (gen_cons bound a) @ (gen_cons bound b)
    | L1 (x, xs) -> (x, "beta_" ^ x) :: (gen_cons (x :: bound) xs)
    | L2 (x, xs) -> (x, "beta_" ^ x) :: (gen_cons (x :: bound) xs)
    | L3 (x, xs) -> (x, "gamma_" ^ x) :: (gen_cons (x :: bound) xs)

let get cons nm = List.assoc cons nm

type ty =
    | Nm of string
    | Arrow of ty * ty

type ty' =
    | Name of string
    | Arr of ty' * ty'
    | Forall of string * ty'

let rec to_ty' = function
    | Nm s -> Name s
    | Arrow (a,b) -> Arr(to_ty' a, to_ty' b)

let rec p_ty' = function
    | Name s -> print_string s
    | Arr(a,b) -> p_ty' a; print_string " -> "; p_ty' b;
    | Forall(a,b) -> print_string a; print_string ". "; p_ty' b

let rec p_ty = function
    | Nm s -> print_string s
    | Arrow(a,b) -> p_ty a; print_string " -> "; p_ty b

type sup =
    | Ineq of ty * ty

let rec p_sup = function
    | Ineq(a,b) -> print_string "("; p_ty a; print_string ") ≤ ("; p_ty b; print_string ")"

let eq s1 s2 =
    let a = fresh() in
    Ineq(Arrow(Nm a,Nm a),Arrow(s1,s2))
    
let ineq a b = Ineq(a,b)

let arr a b = Arrow(a, b)

let rec gen_ineqs cons tm =
    let get = fun z -> 
        match List.assoc_opt z cons with
        | Some n -> n
        | None -> "beta_" ^ z
    in
    match tm with
    | L3(z, n) -> eq (Nm (gen_of tm)) (arr (Nm (get z)) (Nm (gen_of n))) 
        :: gen_ineqs cons n
    | V' s -> ineq (Nm (get s)) (Nm (gen_of tm)) :: []
    | A'(L1(y, e1), e0) -> eq (Nm (get y)) (Nm (gen_of e0)) :: 
        (gen_ineqs cons e1 @ gen_ineqs cons e0)
    | A'(a, b) -> ineq (Nm (gen_of a)) (arr (Nm (gen_of b)) (Nm (gen_of tm))) ::
        (gen_ineqs cons a @ gen_ineqs cons b)
    | L2(_, x) -> gen_ineqs cons x
    | L1(_, x) -> gen_ineqs cons x
    | _ -> []

let rec freshify = function
    | Nm s -> Nm (fresh ())
    | Arrow (a, b) -> Arrow(freshify a, freshify b)

let rec substty tm old nw =
    match tm with
    | Nm s when s = old -> nw
    | Nm _ -> tm
    | Arrow(a,b) -> Arrow(substty a old nw, substty b old nw)

let rec substsup tm old nw =
    print_string ("subst " ^ old ^ " for ");
    p_ty nw;
    print_newline ();
    List.map (fun (Ineq(a,b)) -> Ineq(substty a old nw, substty b old nw)) tm

let subset = ref []
let add a r = subset := (a, r) :: !subset

let rec unify t1 t2 =
    match t1, t2 with
    | Nm a, Nm b -> add b t1; t2
    | Nm _, Arrow _ -> t2
    | Arrow _, Nm _ -> t1
    | Arrow(q,w), Arrow(a,b) -> Arrow(unify q a, unify w b)



let redexI problem a t1 =
    let t1' = freshify t1 in
    add a t1;
    substsup problem a t1'

let redexII problem a t1 t2 =
    let mgu = unify t1 t2 in
    p_ty mgu; print_newline ();
    add a mgu;
    substsup problem a mgu

let rec find_sims t1 t2 =
    match t1, t2 with
    | Nm a, Nm b when a <> b -> (a, Nm b) :: []
    | Arrow(q,w), Nm s -> (s, t1) :: []
    | Arrow(q,w), Arrow(a,b) -> find_sims q a @ find_sims w b
    | _ -> []

let find_sims_ineq (Ineq(a,b)) = find_sims a b

let max_list lst = List.fold_left max 0 lst

let uniq_cons x xs = if List.mem x xs then xs else x :: xs

let remove_dups xs = List.fold_right uniq_cons xs []

let rec solve problem =
    print_endline "\n\nSOLVE:";
    List.iter (fun i -> p_sup i; print_newline ()) problem;
    let sims = List.map find_sims_ineq problem in
    let sims = List.flatten sims |> remove_dups in
    let keys = List.map fst sims in
    let col = List.map ( fun z -> 
        let w = List.filter (fun (a, b) -> a = z) sims in
        let w = List.map snd w in
        (z, w)
    ) keys in
    let len = List.map snd col |> List.map List.length |> max_list in
    if len > 1 then begin
        print_endline "rII";
        let found = List.filter (fun (a,b) -> List.length b > 1) col in
        let use = List.nth found 0 in
        let a = fst use in
        let q = List.nth (snd use) 0 in
        let w = List.nth (snd use) 1 in
        solve (redexII problem a q w)
    end else if len = 1 then begin
        print_endline "rI";
        let found = List.filter (fun (a,b) -> List.length b = 1) col in
        let found = List.filter (fun (a, b) -> match List.nth b 0 with |Nm _ -> false |_ -> true) found in 
        if List.length found = 0 then
            problem
        else
        let use = List.nth found 0 in
        let b = List.nth (snd use) 0 in
        solve (redexI problem (fst use) b)
    end else if len = 0 then
        problem
    else
        raise (Failure (string_of_int len))

let rec apply_subs subset tm =
    match tm with
    | Nm s ->
        begin match List.assoc_opt s subset with
        | Some n when n <> tm -> apply_subs subset n
        | _ -> tm
        end
    | Arrow(a,b) -> Arrow(apply_subs subset a, apply_subs subset b)

let rec get_inner_lam = function
    | L2(_, a) -> get_inner_lam a
    | A'(L1(_, A'(q,w)), _) -> get_inner_lam (A'(q,w))
    | A'(L1(b, a),_) -> Nm (gen_of a)
    | _ -> raise (Failure "get_inner_lam bad theta-conv")

let rec get_l2_types tm = match tm with
    | L2(x, xs) -> Nm (gen_of tm) :: get_l2_types xs
    | _ -> []

let const = L ("ignored", L("const", V "const"))

let example = L ("f", L ("a", L("b", A(A(const, A(V "f", V "a")), A(V "f", V "b")))))

let () = print_endline "\n\n\n\n\nhi\n";
    p_lc example; print_newline ();
    let e = nf example in
    p_llc e; print_newline ();
    let tm = app_theta e in
    p_llc tm; print_newline ();
    let cons = gen_cons [] tm in
    List.iter (fun (nm, ty) -> print_string nm; print_string " : "; print_endline ty) cons;
    let ineqs = gen_ineqs cons tm in
    List.iter (fun i -> p_sup i; print_newline ()) ineqs;
    let _ = solve ineqs in
    let subset = !subset in
    print_endline "subsets:";
    List.iter 
        (fun (a,b) -> print_string a; print_string " = "; p_ty b; print_newline())
        subset; print_newline ();
    let innermost = get_inner_lam tm in
    let typ = apply_subs subset innermost in
    print_endline "type without foralls:";
    p_ty innermost;
    print_string " => ";
    p_ty typ;
    print_newline ();
    let ty' = to_ty' typ in
    let l2_types = get_l2_types tm in
    ()