
let call_ret f = 
  f 100

let main_false ()
(*@ ens res=2 @*)
= let x = ref 0 in
  let swap i =
    let r = !x in
    x := i;
    r
  in
  (* L1 *)
  (* swap 2; *)

  assert (!x = 2);
  (* L2: the call here is only valid after L1*)
  call_ret swap

let main ()
(*@ ens res=2 @*)
= let x = ref 0 in
  let swap i =
    let r = !x in
    x := i;
    r
  in
  (* L1 *)
  swap 2;

  assert (!x = 2);
  (* L2: the call here is only valid after L1*)
  call_ret swap

let main1_false ()
(*@ ens res=1 @*)
= let x = ref 2 in

  let swap i =
    let r = !x in
    x := r - i;
    r
  in

  assert (!x=2);
  call_ret swap;
  assert (!x=3);
  (* the function call is only valid at the first time *)
  1

let main3_false ()
(*@ ens res=1 @*)
= let x = ref 2 in
  assert (!x=2);
  x := !x + 1;
  assert (!x=4);
  1

let main4_false ()
(*@ ens res=1 @*)
= let x = ref 2 in
  assert (!x=2);
  x := 3;
  assert (!x=4);
  1
