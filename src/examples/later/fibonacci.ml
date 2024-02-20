
(* https://arxiv.org/pdf/2104.11050.pdf *)

external fib : int -> int = "fibonacci.Extras.fib"

let rec fib_aux n k x y
= if k = n then !x
  else
    let tmp = !x in
    x := !y;
    y := tmp + !y;
    fib_aux n (k + 1) x y

(*@
    lemma fib_aux_l n k x y res = (* FIXME *)
    fib_aux(n, k, x, y, res) ==>
      ex a; req x->fib(a)*y->fib(a+1)/\a>=0/\k>=0/\k<=n;
      ens x->fib(a+n-k)*y->fib(a+n-k+1)/\res=fib(a+n-k)
@*)

let fib_aux_main n
(*@ req n>=0; ens res=fib(n) @*)
= let x = ref 0 in
  let y = ref 1 in
  fib_aux n 0 x y

let rec fib_iter_aux n k a b
= if k = 0 then !a
  else
    let tmp = !a in
    a := !b;
    b := tmp + !a;
    fib_iter_aux (n + 1) (k - 1) a b

(*@
  lemma fib_iter_aux_spec n k a b res =
    fib_iter_aux(n, k, a, b, res) ==>
      req a->fib(n)*b->fib(n+1)/\k>=0/\n>=0;
      ens a->fib(n+k)*b->fib(n+k+1)/\res=fib(n+k)
@*)

let fib_iter k
(*@ req k>=0; ens res=fib(k) @*)
= let x = ref 0 in
  let y = ref 1 in
  fib_iter_aux 0 k x y

let rec fib_rec_aux n k a b
= if k = 0 then a
  else fib_rec_aux (n + 1) (k - 1) b (a + b)

(*@
  lemma fib_rec_aux_l n k a b res =
    fib_rec_aux(n, k, a, b, res) ==>
      req k>=0/\n>=0/\a=fib(n)/\b=fib(n+1);
      ens res=fib(n+k)
@*)

let fib_rec k
(*@ req k>=0; ens res=fib(k) @*)
= fib_rec_aux 0 k 0 1
