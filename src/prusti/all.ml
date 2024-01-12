
(* https://github.com/FabianWolff/closure-examples/blob/master/all.rs *)

external all : int list -> (int -> bool) -> bool = "all.Extras.all"

(* @ pure all : int list -> (int -> bool) -> bool @*)

let rec all xs pred
= match xs with
| [] -> true
| x :: xs' -> pred x && all xs' pred

(*(*@
  lemma all_all_false xs p res =
   all(xs, p, res) ==> ens res=all(xs, p)
@*)*)

let rec integers n =
  if n <= 0 then []
  else n :: integers (n - 1)

let rec repeat x n =
  if n <= 0 then []
  else x :: repeat x (n - 1)

let is_pos x = x > 0

let has_property p xs = all p xs

let all_pos n (* FIXME *)
(*@ ex r ys; has_property(is_pos, ys, r); ens r=true/\res=ys @*)
= repeat 1 n

(* Unlike pure length, this is not provable because p on the left may have effects *)
let test1 xs
(*@ req xs=[1;2;3;4]; ens res=false @*)
= let is_equal_four v = v = 4 in
  all xs is_equal_four

let test2 xs
(*@ req xs=[1;2;3;4]; ens res=true @*)
= let is_less_than_five v = v < 5 in
  all xs is_less_than_five

let test3 xs
(*@ req xs=[1;2;3;4]; ens res=false @*)
= let is_less_than_three v = v < 3 in
  all xs is_less_than_three
