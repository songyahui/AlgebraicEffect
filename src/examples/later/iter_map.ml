
let rec integers x n =
  if n = 0 then []
  else x :: integers (x + 1) (n - 1)

let rec fill_list f n =
  if n = 0 then []
  else let x = f () in x :: fill_list f (n - 1)

let succ x = x + 1

(* this should work as well but currently doesn't. check forward rule for iter_map succ counter *)
let iter_map_succ x n
(*@ ex i; req x->i; ex r; integers(i+1, n, r) @*)
= let counter =
    fun () ->
      (* the debug is x is not picked up as a used var. because this lambda is collapsed by normalization. because it's not substituted properly but the forward rules apparently *)
      let r = !x in
      x := !x + 1;
      r
  in
  let iter_map f it =
    (* we don't support partial application *)
    let l () = f (it ()) in
    l
  in
  fill_list (iter_map succ counter) n
  
