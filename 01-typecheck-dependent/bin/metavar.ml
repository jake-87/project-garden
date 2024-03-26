type metavar = int
[@@deriving show {with_path = false}]

type 'a metaentry =
  | Unsolved
  | Solved of 'a
[@@deriving show {with_path = false}]

type 'a metactx = (metavar * 'a metaentry) list ref
[@@deriving show {with_path = false}]

let c = ref 0

let next_meta (): metavar =
  incr c;
  !c

let new_metactx ()
  : 'a metactx = ref []

let solve (type t) (mctx: t metactx) (m: metavar) (solution: t) =
  mctx := (m, Solved solution) :: !mctx

let fresh_meta mctx f =
  let m = next_meta () in
  mctx := (m, Unsolved) :: !mctx;
  f m

let lookup (type t) (mctx: t metactx) metavar =
  List.exists (fun (v, _entry) ->
      v = metavar
    ) !mctx 
