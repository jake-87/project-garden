type meta = Metaid of int
[@@deriving show {with_path = false}]

let fresh_meta =
  let i = ref (0) in
  fun () ->
    incr i;
    Metaid (!i)

module Hashtbl = struct
  include Hashtbl

  let pp pp_key pp_value ppf values =
    let as_list =
      Hashtbl.to_seq values
      |> List.of_seq in
    let srt =
      List.sort (fun (Metaid a, _b) (Metaid c, _d) -> Int.compare a c) as_list in
    List.iter (fun (key, data) ->
        Format.fprintf ppf "@[<1>%a: %a@]@." pp_key key pp_value data
      ) srt
end


type 'a metamap = (meta, 'a) Hashtbl.t
[@@deriving show {with_path = false}]

let empty () : 'a metamap = Hashtbl.create 20

let index (map: 'a metamap) (m: meta): 'a 
    = Hashtbl.find map m

let set (map: 'a metamap) (m: meta) (a: 'a): unit =
  Hashtbl.replace map m a

let pp_meta (fmt: Format.formatter) (m: meta) =
  let Metaid i = m in
  Format.fprintf fmt "[%i]" i
