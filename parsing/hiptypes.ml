
open Common

[@@@warning "-17"]

type bin_op = GT | LT | EQ | GTEQ | LTEQ
and term =
    | UNIT 
    | Num of int
    | Var of string
    | Plus of term * term 
    | Minus of term * term 
    | Rel of bin_op * term * term 
    | TTrue
    | TFalse
    | TAnd of term * term
    | TPower of term * term
    | TTimes of term * term
    | TDiv of term * term
    | TOr of term * term
    | TNot of term
    | TApp of string * term list
    | TCons of term * term
    | Nil
    (* the string is just an identifier for uniqueness.
       the last param is the name of the result *)
    | TLambda of string * string list * disj_spec * core_lang option
    (* unused *)
    | TList of term list
    | TTupple of term list

(* (Label n) _k (*@ spec @*) -> e *)
and core_handler_ops = (string * string option * disj_spec option * core_lang) list

(* x :: xs -> e is represented as ("::", [x, xs], e) *)
and constr_cases = (string * string list * core_lang) list

and core_lang = 
      | CValue of core_value 
      | CLet of string * core_lang * core_lang
      | CIfELse of (*core_value*) pi * core_lang * core_lang
      | CFunCall of string * (core_value) list
      | CWrite of string * core_value  
      | CRef of core_value
      | CRead of string 
      | CAssert of pi * kappa 
      | CPerform of string * core_value option
      (* match e with | v -> e1 | eff case... | constr case... *)
      | CMatch of disj_spec option * core_lang * (string * core_lang) option * core_handler_ops * constr_cases
      | CResume of core_value list
      | CLambda of string list * disj_spec option * core_lang

and core_value = term

(* an occurrence of an effect *)
and instant = string * term list


and pi = 
  | True
  | False
  | Atomic of bin_op * term * term
  | And    of pi * pi
  | Or     of pi * pi
  | Imply  of pi * pi
  | Not    of pi 
  | Predicate of string * term list 
  | Subsumption of term * term

and kappa = 
  | EmptyHeap
    (* x -> -   means x is allocated, and - is encoded as Var "_" *)
  | PointsTo of (string * term)
  | SepConj of kappa * kappa
  (*| MagicWand of kappa * kappa*)

(* a formula which describes a program state *)
and state = pi * kappa

(* v->phi and (Eff arg?-> phi)* *)
and handlingcases = (string * disj_spec) * ((string * string option * disj_spec) list)
and trycatch = (spec * handlingcases)


and stagedSpec = 
      | Exists of string list
      | Require of pi * kappa 
      (* ens H /\ P, where P may contain contraints on res *)
      | NormalReturn of (pi * kappa)
      (* higher-order functions: H /\ P /\ f$(...args, term) *)
      (* this constructor is also used for inductive predicate applications *)
      (* f$(x, y) is HigherOrder(..., ..., (f, [x]), y) *)
      | HigherOrder of (pi * kappa * instant * term)
      (* effects: H /\ P /\ E(...args, v), term is always a placeholder variable *)
      | RaisingEff of (pi * kappa * instant * term)
      (* | IndPred of { name : string; args: term list } *)
      | TryCatch of (pi * kappa * trycatch * term)

and spec = stagedSpec list

and disj_spec = spec list

[@@deriving
  visitors { variety = "map"; name = "map_spec" },
  visitors { variety = "reduce"; name = "reduce_spec" } ]

(* not part of the visitor because this doesn't occur recursively *)
type typ =
  | Unit
  | List_int
  | Int
  | Bool
  | Lamb
  | Arrow of typ * typ
  | TVar of string (* this is last, so > concrete types *)
[@@deriving show { with_path = false }, ord]

[@@@warning "+17"]

let min_typ a b = if compare_typ a b <= 0 then a else b

let is_concrete_type = function TVar _ -> false | _ -> true

let concrete_types = [Unit; List_int; Int; Bool; Lamb]

let res_v = Var "res"

let z3_consumption = ref 0.0

let summary_forward = ref 0.0
let summary_entail = ref 0.0
let summary_askZ3 = ref 0.0



let res_eq t = Atomic (EQ, res_v, t)



module U = struct
  include UnionFind

  let merge f a b = ignore (merge f a b)
end

module TMap = Map.Make (struct
  type t = typ

  let compare = compare_typ

end)

(* A map giving type variables possibly-concrete types *)
module TEnv = struct

  type t = typ U.elem TMap.t ref

  let create () =
    (* TMap.empty *)
    TMap.of_seq (List.to_seq (List.map (fun t -> t, U.make t) concrete_types))

  let get_or_create m k =
    match TMap.find_opt k !m with
    | None ->
      let r = U.make k in
      m := TMap.add k r !m;
      r
    | Some v ->
      v

  let equate m t1 t2 =
    let t1r = get_or_create m t1 in
    let t2r = get_or_create m t2 in
    U.merge min_typ t1r t2r

  let concretize m t = TMap.find t !m |> U.get

  let has_concrete_type m t =
    match TMap.find_opt t !m with
    | None -> false
    | Some r -> is_concrete_type (U.get r)

end

type abs_typ_env = {
  (* formula variable -> type, which may be a variable *)
  vartypes: typ SMap.t;
  (* types of type variables so far *)
  equalities : TEnv.t;
}

let create_abs_env () =
  {
    vartypes = SMap.empty;
    equalities = ref (TEnv.create ()) ;
  }

(* concrete type environment, where every variable has a concrete type *)
type typ_env = typ SMap.t

[@@@warning "-17"]

(* type effectStage =  (string list* (pi * kappa ) * (pi * kappa) * instant * term) *)
type effectStage = {
  e_evars : string list;
  e_pre : pi * kappa;
  e_post : pi * kappa;
  e_constr : instant;
  e_ret : term;
  e_typ : [`Eff | `Fn] [@opaque];
}
[@@deriving
  visitors { variety = "map"; name = "map_effect_stage_" },
  visitors { variety = "reduce"; name = "reduce_effect_stage_" }]

type tryCatchStage = {
  tc_evars : string list;
  tc_pre : pi * kappa;
  tc_post : pi * kappa;
  tc_constr : trycatch;
  tc_ret : term;
}
[@@deriving
  visitors { variety = "map"; name = "map_try_catch_stage_" },
  visitors { variety = "reduce"; name = "reduce_try_catch_stage_" }]


type effHOTryCatchStages = EffHOStage of effectStage | TryCatchStage of tryCatchStage
[@@deriving
  visitors { variety = "map"; name = "map_eff_stages_" },
  visitors { variety = "reduce"; name = "reduce_eff_stages_" }]

(** existentials, pre, post (which may contain constraints on res) *)
type normalStage =  (string list* (pi * kappa ) * (pi * kappa))
[@@deriving
  visitors { variety = "map"; name = "map_normal_stages_" },
  visitors { variety = "reduce"; name = "reduce_normal_stages_" }]

type normalisedStagedSpec = effHOTryCatchStages list * normalStage
[@@deriving
  visitors { variety = "map"; name = "map_normalised_" },
  visitors { variety = "reduce"; name = "reduce_normalised_" }]

[@@@warning "+17"]

class virtual ['self] reduce_normalised =
  object (_ : 'self)
    inherit [_] reduce_spec
    inherit! [_] reduce_effect_stage_
    inherit! [_] reduce_try_catch_stage_
    inherit! [_] reduce_eff_stages_
    inherit! [_] reduce_normal_stages_
    inherit! [_] reduce_normalised_
  end

class virtual ['self] map_normalised =
  object (_ : 'self)
    inherit [_] map_spec
    inherit! [_] map_effect_stage_
    inherit! [_] map_try_catch_stage_
    inherit! [_] map_eff_stages_
    inherit! [_] map_normal_stages_
    inherit! [_] map_normalised_
  end

let freshNormalReturnSpec = [NormalReturn (True, EmptyHeap)]
let freshNormalStage : normalStage = ([], (True, EmptyHeap), (True, EmptyHeap)) 

let freshNormStageRet r : normalStage = ([], (True, EmptyHeap), (res_eq r, EmptyHeap)) 



type tactic =
  | Unfold_right
  | Unfold_left
  | Apply of string
  | Case of int * tactic

type meth_def = {
  m_name : string;
  m_params : string list;
  m_spec : disj_spec option;
  m_body : core_lang;
  m_tactics : tactic list;
}

(** A predicate is a name for a parameterized disjunctive staged spec of the form [f(x, ...) == spec \/ ...].
    Predicates are checked or inferred for effectful functions and remembered after. *)
type pred_def = {
  p_name: string;
  p_params: string list; (* list to ensure ordering. last param is typically a return value *)
  p_body: disj_spec;
  p_rec: bool;
}

type sl_pred_def = {
  p_sl_ex: string list;
  p_sl_name: string;
  p_sl_params: string list; (* list to ensure ordering. last param is typically a return value *)
  p_sl_body: pi * kappa;
}

(** A pure function that can be imported directly into SMT *)
type pure_fn_def = {
  pf_name: string;
  pf_params: (string * typ) list;
  pf_ret_type: typ;
  pf_body: core_lang;
}

type pure_fn_type_def = {
  pft_name: string;
  pft_logic_path: string list;
  pft_logic_name: string;
  pft_params: typ list;
  pft_ret_type: typ;
}

(** A lemma is an entailment [f(x, ...) <: spec]. The left side is restricted to be a function stage (without loss of generality). Some of x, ... may be parameters, but some may not be. *)
type lemma = {
  l_name: string;
  l_params: string list; (* ordered, the last parameter is a result *)
  l_left: instant; (* for simplicity of rewriting *)
  l_right: spec; (* could also be disj_spec but not needed *)
}

type core_program = {
  cp_effs: string list;
  cp_predicates: pred_def SMap.t;
  cp_sl_predicates: sl_pred_def SMap.t;
  cp_lemmas: lemma SMap.t;
  cp_methods: meth_def list;
}

let empty_program = {
  cp_effs = [];
  cp_methods = [];
  cp_predicates = SMap.empty;
  cp_sl_predicates = SMap.empty;
  cp_lemmas = SMap.empty
}

include Common

type 'a quantified = string list * 'a

type instantiations = (string * string) list

let primitive_functions = ["+"; "-"; "="; "not"; "::"; "&&"; "||"; ">"; "<"; ">="; "<="]