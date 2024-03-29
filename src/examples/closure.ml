
let closures ()
(*@ ex i; Norm(i->[8;7;42], [8;7;42]) @*)
= let l = ref [] in
  l := 42 :: !l;
  let f i = l := i :: !l in
  let g h x = h x; l := (x+1) :: !l in
  g f 7;
  (* assert (!l = [8;7;42]); *)
  !l

let closures_with_local_state ()
(*@ ex i j; Norm(i->1 * j->2, 3) @*)
= let f =
    let x = ref 0 in
    fun () -> x := !x + 1; !x
  in
  let g =
    let x = ref 0 in
    fun () -> x := !x + 2; !x
  in
  f () + g ()

let simple_closures ()
(*@ Norm(emp, 4) @*)
= let counter =
    let x = ref 0 in
    fun () -> let r = !x in x := !x + 1; r
  in
  let x = ref 3 in
  counter ();
  counter () + !x

(* Section 2.2.1 in Modular Specification and Verification of Closures in Rust *)
let closure_with_effects ()
(*@ ex i j; ens i->2*j->3/\res=5 @*)
= let i = ref 1 in
  let j = ref 2 in
  let cl x
  (*@
    ex a b; req x->a*j->b; ens j->b+a * x->a+1 /\  res=b+a+a+1
    \/ ex a; req x->a /\ x=j; ens j->a+a+1 /\ res=a+a+1+a+1
  @*)
  = j := !j + !x;
    x := !x + 1;
    !j + !x in
  cl i

(* Section 3.2 in Modular Specification and Verification of Closures in Rust *)
let closure_with_history_invariant i j
(*@ ex iv jv; req i->iv*j->jv; ens i->1*j->2 @*)
= let count = ref 0 in
  let cl ()
  (*@ ex a; req count->a; ens count->a+1/\res=a+1 @*)
  = count := !count + 1;
    !count in
  i := cl();
  j := cl()

(* Section 3.3 in Modular Specification and Verification of Closures in Rust *)
let roll_dice () (*@ ens res>0 @*) = 4 (* FIXME: Should be random *)
let call_ret f
(*@ req f <: (fun v r (*@ req v>0; ens r>0 @*)) @*)
= let x = roll_dice () in f x

let closure_with_hof_false ()
(*@ ens T @*)
= let x = ref (-1) in
  let cl i = let r = !x in x := !x + i; r in
  (* x is still -1 *)
  call_ret cl

let closure_with_hof_ok ()
= let x = ref (-1) in
  let cl i = let r = !x in x := !x + i; r in
  cl 2; (* x is now 1 *)
  call_ret cl

(* https://ilyasergey.net/CS6217/_static/slides/04-FunLog.pdf *)
let min_max_plus x y min max
(*@ ex a b; req min->a*max->b; ex i j; ens min->i*max->j/\i<=j/\res=x+y @*)
= let min' = if x < y then x else y in
  let max' = if x < y then y else x in
  min := min';
  max := max';
  x + y
