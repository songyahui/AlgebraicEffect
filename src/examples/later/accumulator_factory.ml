
(* https://rosettacode.org/wiki/Accumulator_factory *)

let accumulator init =
  let total = ref init in
  let acc x
  (*@ ex t; req total->t; ens total->t+x/\res=t+x @*)
  = total := !total + x; !total in
  acc

let test x n init (* FIXME *)
(*@ req n>=0; ens res=init+(n*.x) @*)
= let acc = accumulator init in
  let rec repeat x k
  = if k = 0 then acc 0
    else (acc x; repeat x (k - 1))
  in
  repeat x n
