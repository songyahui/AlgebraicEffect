
  $ check() { TEST=1 hip "$1" 2>&1; }
  $ sanitize() { grep Time; }
  $ output() { hip "$1" 2>&1 | sanitize; }
  $ check_why3_only() { if [ "$PROVER" = "WHY3" ]; then check "$1"; else echo "ALL OK!"; fi; }

  $ check test_new_entail.ml
  ALL OK!

  $ check test_ho.ml
  ALL OK!

  $ check test_lists.ml
  ALL OK!

  $ check test_match.ml
  ALL OK!

  $ check_why3_only test_lambda.ml
  ALL OK!

  $ check test_closures.ml
  ALL OK!

  $ check ../evaluation/0_heap_zero_once_twice.ml
  ALL OK!

  $ check ../evaluation/1_heap_zero_once_twice.ml
  ALL OK!

  $ check ../evaluation/2_heap_zero_once_twice.ml
  ALL OK!

  $ check ../evaluation/3_nestedHandlers.ml
  ALL OK!

  $ check ../evaluation/4_memory_cell.ml
  ALL OK!

  $ check ../evaluation/5_memory_cell.ml
  ALL OK!

  $ check ../evaluation/6_memory_cell_mix_handler.ml
  ALL OK!

  $ check ../evaluation/7_memory_cell_mix_handler.ml
  ALL OK!

  $ check ../evaluation/8_memory_cell_nested.ml
  ALL OK!

  $ check ../evaluation/9_memory_cell_nested.ml
  ALL OK!

  $ check ../evaluation/10_memory_cell_nested.ml
  ALL OK!

  $ check ../evaluation/11_exchange.ml
  ALL OK!

  $ check ../evaluation/12_two_pointers.ml
  ALL OK!

This requires the power axioms

$ check ../../benchmarks/effects/ocaml412/A_generic_count.ml
FAILED: main

We can't handle these cases yet

$ check ../examples/calls.ml
ALL OK!

  $ check ../examples/compose.ml
  ALL OK!

  $ check ../examples/applyN.ml
  ALL OK!

  $ check ../examples/map.ml
  ALL OK!

  $ check ../examples/length.ml
  ALL OK!

  $ check ../examples/calls.ml
  ALL OK!

  $ check ../examples/closure.ml
  ALL OK!

  $ check ../examples/fold.ml
  ALL OK!

  $ check ../examples/iter.ml
  ALL OK!

  $ check ../examples/exception.ml
  ALL OK!

  $ check_why3_only ../prusti/all.ml
  ALL OK!

  $ check ../prusti/blameassgn.ml
  ALL OK!

  $ check ../prusti/counter.ml
  ALL OK!

  $ check ../prusti/cl_returned.ml
  ALL OK!

  $ check ../prusti/repeat_with_n.ml
  ALL OK!

  $ check_why3_only ../examples/length_pure.ml
  ALL OK!

This does not work yet

$ check ../examples/all.ml
ALL OK!

  $ check ../evaluation/abort.ml
  ALL OK!
