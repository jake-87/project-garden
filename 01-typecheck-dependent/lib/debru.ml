module S = Syntax
module D = Domain

(* convert between debru indexes and levels
   this confuses me every time, so i'm glad to have it as a library lol
*)

let lvl2ix' len (D.Lvl i) = S.Ix (len - i - 1)
let lvl2ix (D.Lvl len) (D.Lvl i) = S.Ix (len - i - 1)
let ix2lvl len (S.Ix i) = D.Lvl (len - i - 1)
