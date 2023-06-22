
let roll_dice () = 100

let call_ret f = 
  let x = roll_dice () in 
  f x

let main ()
(*@ Norm(emp, 2) @*)
= let x = ref 0 in
  let cl i = 
    let r = !x in 
    x := i; 
    r
  in
  (* L1 *)
  cl 2;

  assert (!x = 2);
  (* L2: the call here is only valid after L1*)
  call_ret cl