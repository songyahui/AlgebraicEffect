
let[@pure] rec length (xs: int list): int
= match xs with
  | [] -> 0
  | x :: xs1 -> 1 + length xs1

let rec append xs ys =
  match xs with
  | [] -> ys
  | x :: xs' -> x :: append xs' ys

(* Example 6.3 *)
let rec take xs n
= if n = 0 then [] else match xs with
| [] -> []
| x :: xs' -> x :: take xs' (n - 1)

let take_spec xs n
(*@ req n>=0/\n<=length(xs); ex r; ens res=r @*)
= take xs n

let rec drop xs n
= if n = 0 then xs else match xs with
| [] -> []
| x :: xs' -> drop xs' (n - 1)

let drop_spec xs n
(*@ req n>=0/\n<=length(xs); ex r; ens res=r @*)
= drop xs n

let append_take_drop xs n (* FIXME: By induction *)
(*@ ens res=xs @*)
= append (take_spec xs n) (drop_spec xs n)

let take_drop_append1 xs ys (* FIXME *)
(*@ ens res=xs @*)
= take_spec (append xs ys) (length xs)

let take_drop_append2 xs ys (* FIXME *)
(*@ ens res=ys @*)
= drop_spec (append xs ys) (length xs)
