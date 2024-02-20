
effect Eff : unit 

(* basic *)

let test10 ()
  (*@ Norm(emp, 0) @*) =
  0
(* implicit normal stage *)

let test10_s ()
  (*@ Norm(emp/\res=0) @*) =
  0
(* res can also be used *)

let test10_p ()
  (*@ Norm(res=0) @*) =
  0
(* emp can be omitted *)

let test10_ens_p ()
  (*@ ens res=0 @*) =
  0
(* ens can be used *)

let test6 ()
  (*@ Norm(emp, 0) @*) =
  let j = 0 in
  j
(* intermediate bindings don't matter *)

let test7_false ()
  (*@ Norm(emp, j) @*) =
  let j = 0 in
  j
(* j is not a param *)

let test8_false ()
  (*@ Norm(emp, k) @*) =
  let j = 0 in
  j
(* k is not a param *)

let test9 ()
  (*@ ex r; Norm(emp, r) @*) =
  let j = 0 in
  j
(* existential return value *)

let test4 ()
  (*@ ex i; Norm(i->0, i) @*) =
  let i = ref 0 in 
  i
(* new heap location, hence existential *)

let test5 ()  (*@ ex i; Norm(i->0, 1) @*) =
  let i = ref 0 in 
  !i + 1
(* heap read *)

let test61 ()  (*@ ex i; Norm(i->1, 1) @*) =
  let i = ref 0 in 
  i := !i + 1;
  !i
(* heap update *)

let test23_false ()  (*@ ex i; Norm(i->1, 1) @*) =
  let i = ref 0 in 
  i := !i + 2;
  !i
(* wrong value *)

let test19 ()  (*@ ex r; Eff(emp, r) @*) =
  let ret = perform Eff in
  ret
(* this is the only correct implementation. note that the spec is implicitly completed with ... Norm(emp, r), the return value of the previous stage. *)

let test27 ()  (*@ ex r; Eff(emp, r); ex r1; Norm(emp, r1) @*) =
  let ret = perform Eff in
  1
(* if we explicitly give a Norm, the return value of perform and the function can differ *)

let test25 ()  (*@ Eff(emp, ()) @*) =
  let ret = perform Eff in
  ret
(* this can be proved in why3 due to it leveraging type information - since ret is of type unit, its value must be (). our z3 encoding is wrong since we encode unit as int *)

let test12_false ()  (*@ Eff(emp, ()) @*) =
  let ret = perform Eff in
  1
(* this fails with a type error in why3, as it should *)

let test21 ()  
(*@ ex i ret;
   Eff(i->0, ret);
   req i-> z; 
   Norm(i->z+1, ret)
@*)
= 
  let i = Sys.opaque_identity (ref 0) in 
  let ret = perform Eff in 
  i := !i + 1;
  ret

let test0 ()  
(*@ ex i z ret;
   Eff(i->0, ret);
   req i-> z; 
   Norm(i->z+1, ret)
@*)
= 
  let i = Sys.opaque_identity (ref 0) in 
  let ret = perform Eff in 
  i := !i + 1;
  ret

let test1_false ()  
(*@ ex i z ret;
   Eff(i->0, ret);
   req i-> z; 
   Norm(i->z+1, ret)
@*)
= 
  let i = Sys.opaque_identity (ref 0) in 
  let ret = perform Eff in 
  i := !i + 1;
  !i (* wrong *)

let test2_false ()  
(*@ ex i z ret;
   Eff(i->0, ret);
   req i-> z; 
   Norm(i->z+1, ret)
@*)
= 
  let i = Sys.opaque_identity (ref 0) in 
  let ret = perform Eff in 
  (* state unchanged *)
  ret

let test3_false ()  
(*@ ex i z ret;
   Eff(i->0, ret);
   req i-> z; 
   Norm(i->z+1, ret)
@*)
= 
  let i = Sys.opaque_identity (ref 0) in 
  let ret = perform Eff in 
  i := !i + 2; (* wrong state *)
  ret

let test13 ()  
(*@ ex a b;
   Norm(a->0 * b->1, 1)
@*)
= 
  let i = ref 0 in 
  let j = ref 1 in 
  1

let test18 ()  
(*@ ex a b;
   Norm(a->1+1 * b->0, 1)
@*)
= 
  let i = ref 0 in 
  let j = ref 2 in 
  1

let test20 ()
(*@ ex b;
   req i->1;
   Norm(i->1 * b->2, 1)
@*)
=
  assert (i-->1);
  let j = ref 2 in 
  1

let test21 ()
(*@ ex b;
   req i->1;
   Norm(i->1 * b->2, 1)
@*)
=
  assert (!i = 1);
  let j = ref 2 in 
  assert (!j = 2);
  1

let test22 ()
(*@ ex i a;
   Norm(i->a, ())
@*)
=
  let j = ref 2 in 
  let z = !j in
  assert (!j = z)

let test14_false ()  
(*@ ex a b;
   Norm(a->1 * b->1, 1)
@*)
= 
  let i = ref 0 in 
  let j = ref 1 in 
  1

let test15 ()  
(*@
   req a->1;
   Norm(a->1, 1)
@*)
= 
  assert (a-->1);
  1

(* this is unintuitive, but true as a consequence of the frame rule *)
let test16 ()  
(*@ ex a;
   req a->1;
   Norm(a->1, 1)
@*)
= 
  let i = ref 0 in 
  1

let test17 ()  
(*@ ex b;
   req a->1;
   Norm(a->1 * b->0, 1)
@*)
= 
  assert (a-->1);
  let i = ref 0 in 
  1

let f1 () (*@ Norm(emp, 1) @*) = 1

let test24 ()  (*@ Norm(emp, 1) @*) =
  let ret = f1 () in
  ret

let fa a (*@ req a=1/\emp; Norm(emp, 2) @*) = a + 1

let test26 ()  (*@ Norm(emp, 2) @*) =
  let ret = fa 1 in
  ret

let two_locations () 
(*@ ex i j z1 z2 ret;
   E(i->0 * j->0, ret);
   req i->z1 * j->z2; 
   Norm(i->z1+1*j->z2+1, ret)
@*)
= let i = ref 0 in 
  let j = ref 0 in 
  let ret = perform E in 
  i := !i + 1;
  j := !j + 1;
  ret

let if_disj b
(*@ Norm(emp, 1) \/ Norm(emp, 2)
@*)
= if b then 1 else 2

let if_let x
(*@ Norm(emp, 1) \/ Norm(emp, 2) @*)
= let y = not x in
  if y then 1 else 2

let foo1 xs = 1
let foo2 xs (*@ ens res=1 @*) = 1

let goo1 xs
(*@ ex t; foo1(xs, t); ens res=t @*)
= foo1 xs

let goo2 xs
(*@ ex t; foo2(xs, t); ens res=t @*)
= foo2 xs

let call_f_in_g ()
(*@ ens res=5 @*)
= let x = 3 in
  let f x = x in
  f 5

let call_ret f (* ex v; f(100,v); ens res=v *) =
  f 100

let test_non_rec_pred ()
(*@ ens res=100 @*)
= let id i = i in
  id 2;

  call_ret id
