type metavar = int ref
[@@deriving show {with_path = false}]

type 'a metaentry =
  | Unsolved
  | Solved of 'a

type 'a metactx = (metavar * 'a metaentry) list ref

let c = ref 0

let next_meta (): metavar =
  incr c;
  ref @@ !c

let new_metactx ()
  : 'a metactx = ref []

let fresh_meta mctx f =
  let m = next_meta () in
  mctx := (m, Unsolved) :: !mctx;
  f m

let lookup (type t) (mctx: t metactx) metavar =
  List.exists (fun (v, entry) ->
      v = metavar
    ) !mctx 
