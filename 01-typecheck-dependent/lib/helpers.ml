exception Sorry of string

let sorry s = raise (Sorry s)

exception Cannot of string

let cannot s = raise (Cannot s)
