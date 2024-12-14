Require Import Nat.

Inductive symbol : Type :=
   | Zero
   | One
   | Blank.
   
Inductive halt : Type := 
  | Running
  | Halted.
   
Definition state : Type := sum nat unit.

Inductive direction : Type :=
  | L | R.
  
Inductive op : Type :=
  | W0
  | W1
  | N.
  
Record tape: Type := {
  left: list symbol ;
  curr: symbol ;
  right: list symbol ;
  }.
  
Definition shl : tape -> tape := fun t =>
  match left t with
  | nil => {|
      left := nil;
      curr := Blank;
      right := cons (curr t) (right t);
    |}
  | cons x xs =>
    {|
      left := xs;
      curr := x;
      right := cons (curr t) (right t);
    |}
  end.
  
Definition shr : tape -> tape := fun t =>
  match right t with
  | nil => 
    {|
      left := cons (curr t) (left t);
      curr := Blank;
      right := nil;
    |}
  | cons x xs =>
    {|
      left := cons (curr t) (left t);
      curr := x;
      right := xs;
    |}
  end.
  
Definition get : tape -> symbol := fun t => (curr t).
  
Definition op_tape : tape -> op -> tape := fun t o =>
  match o with
  | W0 => {|
    left := left t;
    curr := Zero;
    right := right t;
  |}
  | W1 => {|
    left := left t;
    curr := One;
    right := right t;
  |}
  | N => t
  end.
  
Definition move : tape -> direction -> tape := fun t d =>
  match d with
  | L => shl t
  | R => (shr t)
  end.
  
Definition transition : Type := state -> symbol -> (state * op * direction).

Record TM : Type := {
  tp: tape;
  trans: transition;
  st: state;
  halted: halt;
}.

Definition reduce (t: TM): TM :=
  match halted t with
  | Halted => t
  | Running =>
    let tp := tp t in
    let sym := get tp in
    let st := st t in
    match (trans t) st sym with
    | (st, op, dir) =>
      let halted' := match st with
      | inr tt => Halted
      | inl _ => Running
        end in
      let tp' := op_tape tp op in
      match move tp' dir with
      mv =>
      {|
        tp := mv;
        trans := trans t;
        st := st;
        halted := halted'
      |}
      end
    end
  end.

Arguments reduce: simpl nomatch.

Fixpoint reduce_n (t: TM) (n: nat) : TM :=
  match n with
  | 0 => t
  | S n =>
    reduce_n (reduce t) (n - 1)
  end.

Definition Halts (tm: TM) := exists n, (st (reduce_n tm n) = inr tt).

Definition boring : transition := fun _ _ => (inr tt, N, R).

Definition from_trans (t: transition) (st: state) := 
  {|
    tp := {| left := nil; curr := Blank; right := nil |};
    trans := t;
    st := st;
    halted := Running;
  |}.

Lemma boring_halts : Halts (from_trans boring (inl 0)).
Proof.
  unfold Halts, from_trans.
  exists 1.
  auto.
Qed.
Require Import Coq.Program.Equality.
Require Import Setoid.
Require Import Psatz.
Lemma duh : forall n, n <> 0 -> S (n - 1) = n.
Proof.
intros.
lia.
Qed.

Lemma self_reduction : forall tm n, reduce tm = tm -> reduce_n tm n = tm.
Proof.
  intros tm n H.
  rewrite<- H at 2.
  unfold reduce_n.
  induction n.
  - rewrite H; easy.
Abort.
