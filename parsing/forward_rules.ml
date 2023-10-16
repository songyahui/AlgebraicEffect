
open Hipcore
open Hiptypes
open Pretty
open Normalize
include Subst
open Debug


let concatenateSpecsWithEvent (current:disj_spec) (event:spec) : disj_spec = 
  List.map (fun a -> List.append a event) current

let concatenateEventWithSpecs  (event:spec) (current:disj_spec) : disj_spec = 
  List.map (fun a -> List.append event a ) current


let concatenateSpecsWithSpec (current:disj_spec) (event:disj_spec) :  disj_spec = 
  List.concat_map (fun a -> concatenateSpecsWithEvent current a) event

let rec retrieve_return_value (spec:spec) : term = 
  match spec with 
  | [] -> failwith "retrieve_return_value empty spec"
  | [NormalReturn (pi, _)] -> get_res_value pi
  | [HigherOrder (_, _, _, retN)]
  | [RaisingEff(_, _, _, retN)] -> retN
  | _ :: xs -> retrieve_return_value xs 

let rec replace_return_value (t:term) (spec:spec) : spec = 
  match spec with 
  | [] -> failwith "replace_return_value empty spec"
  | [HigherOrder (p, h, i, _)] -> [HigherOrder (p, h, i, t)]
  | [NormalReturn (p, h)] -> [NormalReturn (p, h)]
  | [RaisingEff(p, h, i, _)] -> [RaisingEff (p, h, i, t)]
  | s :: ss -> s :: replace_return_value t ss

(** add an equality to v to the end of all disjuncts *)
let constrain_final_res (sp:disj_spec) (v:term) : disj_spec =
  sp |> List.map (fun s ->
    let l = List.length s in
    s |> List.mapi (fun i a -> if i < l-1 then a else
      match a with
      | Exists _ -> a
      | Require (_, _) -> a
      | NormalReturn (p, h) ->
        NormalReturn (And (p, res_eq v), h)
      | HigherOrder (p, k, (c, va), r) ->
        HigherOrder (And (p, Atomic (EQ, r, v)), k, (c, va), r)
      | RaisingEff (p, k, (c, va), r) ->
        RaisingEff (And (p, Atomic (EQ, r, v)), k, (c, va), r)))

(** Environment used for forward verification *)
type fvenv = {
  (* defined methods, may be added to if lambdas are given names *)
  fv_methods : meth_def SMap.t;

  (* definitions of lambda terms (which are opaque to smt),
     added to when lambdas are defined *)
  fv_lambda : meth_def SMap.t;

  (* methods which need to be changed if a lambda is changed, e.g. by substitution *)
  fv_lambda_names : (string * string) list;

  (* proof obligations generated by defining lambdas with specifications.
     we propagate them out instead of checking them immediately to avoid a cyclic dependency with entailment. *)
  fv_lambda_obl : (disj_spec * disj_spec) list;

  (* proof obligations generated by user-supplied match specs *)
  fv_match_obl : (disj_spec * disj_spec) list;
}

let create_fv_env fv_methods = {
  fv_methods;
  fv_lambda = SMap.empty;
  fv_lambda_obl = [];
  fv_match_obl = [];
  fv_lambda_names = [];
}

let retrieveSpecFromEnv (fname: string) (env:fvenv) : (string list * spec list) option = 
  SMap.find_opt fname env.fv_methods
  |> Option.map (fun m -> (m.m_params, Option.get m.m_spec))


let bindFormalNActual (formal: string list) (actual: core_value list) : ((string * core_value) list)= 
  List.map2 (fun a b -> (a, b)) formal actual

let bindNewNames (formal: string list) (actual: string list) : ((string * string) list)= 
  List.map2 (fun a b -> (a, b)) formal actual




  







let rec getExistientalVar (spec:normalisedStagedSpec) : string list = 
  let (effS, normalS) = spec in 
  match effS with 
  | [] -> 
    let (ex, _, _) = normalS in ex 
  | eff :: xs -> 
    eff.e_evars @ getExistientalVar (xs, normalS)




let instantiateExistientalVarSpec   (spec:spec) 
(bindings:((string * string) list)): spec = 
  let normalSpec = normalise_spec spec in 
  normalisedStagedSpec2Spec (instantiateExistientalVar normalSpec bindings)



let isFreshVar str : bool = 
  if String.length str < 1 then false 
  else 
    let a = String.get str 0 in 
    (*let b = String.get str 1 in *)
    if a='f' (*&& b ='f'*) then true else false 

let () = assert (isFreshVar "f10" ==true )
let () = assert (isFreshVar "s10" ==false )

(** substitutes existentials with fresh variables *)
let renamingexistientalVar (specs:disj_spec): disj_spec = 
  (* Format.printf "specs: %s@." (string_of_disj_spec specs); *)
  List.map (
    fun spec -> 
      (* Format.printf "spec: %s@." (string_of_spec spec); *)
      let normalSpec = normalise_spec spec in 
        (* Format.printf "normalSpec: %s@." (string_of_normalisedStagedSpec normalSpec); *)
      let existientalVar = getExistientalVar normalSpec in 
      (* Format.printf "existientalVar: %s@." ( string_of_list Fun.id existientalVar); *)
      let newNames = List.map (fun n -> (verifier_getAfreeVar n)) existientalVar in 
      let newNameTerms = List.map (fun a -> Var a) newNames in 
      let bindings = bindNewNames existientalVar newNames in 
      let temp = instantiateExistientalVar normalSpec bindings in 
        (* Format.printf "temp: %s@." (string_of_normalisedStagedSpec temp); *)
      let bindings = bindFormalNActual existientalVar newNameTerms in 
      let r = 
      instantiateSpec bindings (normalisedStagedSpec2Spec temp)
      in
        (* Format.printf "r: %s@." (string_of_spec r); *)
      r
  ) specs

(** substitutes existentials with fresh variables, and the resulting formula has no quantifiers *)
let freshen (specs:disj_spec): disj_spec = 
  renamingexistientalVar specs
  |> List.map (List.filter (function Exists _ -> false | _ -> true))


let instantiate_higher_order_functions fname fn_args (spec:disj_spec) : disj_spec =
  let rec loop (acc:stagedSpec Acc.t list) (ss:spec) =
    match ss with
    | [] -> List.map Acc.to_list acc
    | s :: ss1 ->
      (match s with
      | Exists _ | Require (_, _) | NormalReturn _ | RaisingEff _ ->
        loop (List.map (fun tt -> Acc.add s tt) acc) ss1
      | HigherOrder (p, h, (name, args), ret) ->
        let matching = List.find_map (fun (mname, mspec) ->
          match mspec with
          | Some (mparams, msp) when String.equal mname name && List.length mparams = List.length args ->
          Some (mparams, msp)
          | _ -> None) fn_args
        in
        (match matching with
        | None ->
          loop (List.map (fun tt -> Acc.add s tt) acc) ss1
        | Some (mparams, mspec) ->
          let bs = bindFormalNActual mparams args in
          let instantiated = instantiateSpecList bs (renamingexistientalVar mspec)
            (* replace return value with whatever x was replaced with *)
          in
          let res = acc |> List.concat_map (fun tt ->
            List.map (fun dis -> tt |> Acc.add (NormalReturn (p, h)) |> Acc.add_all dis) instantiated)
          in
          let ret1 = match ret with Var s -> s | _ -> failwith (Format.asprintf "return value of ho %s was not a var" (string_of_term ret)) in
          (* instantiate the return value in the remainder of the input before using it *)
          let ss2 =
            let bs = List.map (fun s -> (ret1, retrieve_return_value s)) instantiated in
            instantiateSpec bs ss1
          in
          loop res ss2))
  in
  (* in acc, order of disjuncts doesn't matter *)
  let res = List.concat_map (fun ss -> loop [Acc.empty] ss) spec in
info ~title:(Format.asprintf "instantiate higher order function: %s" fname) "args: %s\n\n%s\n==>\n%s" (string_of_list (string_of_pair Fun.id (string_of_option (string_of_pair (string_of_list Fun.id) (string_of_list string_of_spec)))) fn_args) (string_of_disj_spec spec) (string_of_disj_spec res);
  res

(** Find the case that handles the effect [label] *)
let lookforHandlingCases ops (label:string) = 
  List.find_map (fun (s, arg, spec) ->
    if String.equal s label then Some (arg, spec) else None) ops

(* let (continueationCxt: ((spec list * string * (string * core_lang) * core_handler_ops) list) ref)  = ref []  *)

let map_state env f xs =
  let r, env =
    List.fold_right (fun c (t, env) ->
      let r, e1 = f c env
      in (r :: t, e1)
    ) xs ([], env)
  in
  r, env

(** Like concat_map, but threads an extra "environment" argument through which can be updated by the function *)
let concat_map_state env f xs =
  let r, env = map_state env f xs in
  List.concat r, env

let%expect_test _ =
  let r, e = (concat_map_state 0 (fun x e -> [x; x * 3], e + 1) [1; 2; 3]) in
  Format.printf "%s %d@." (string_of_list string_of_int r) e;
  [%expect
    {| [1; 3; 2; 6; 3; 9] 3 |}]

let foldl1 f xs =
  match xs with
  | [] -> failwith "foldl1"
  | x :: xs1 ->
    List.fold_left f x xs1

let primitives = ["+"; "-"; "="; "not"; "::"; "&&"; "||"; ">"; "<"; ">="; "<="]

(* Given the specs of the scrutinee, symbolically execute it against the handler's spec to produce a single flow, e.g.

    match A(a,r); ens res=c with
    | A d -> continue(f,g); ens res=g
    | v -> v

    first, handle A. we need [d:=a] to bind the argument in the handler branch, and [r:=f] to pass back the argument from continue.

    this gives us a flow like the following, due to deep handling:

    ens d=a /\ r=f;
      match continue(f,g) with
      | ...
    ; ens res=g

    the spec of the continue is (ens res=c), the rest of the scrutinee after A. replace the continue stage with ens res=c.

    ens d=a /\ r=f;
      match ens res=c with
      | v -> ens res=v
      | ...
    ; ens res=g 

    now recursively handle the continue. the base case occurs when there are no more effects to handle. substitute [v:=c] in the value branch.
    c will then be returned from the (substituted-away) continue stage, so [res:=g], resulting in this trace.

    ens d=a /\ r=f; ens g=c; ens res=g

    the actual code below handles extra complexity such as the scrutinee having disjunction, multiple continue stages, res not being an equality (in which case "bridging" fresh variables are needed), freshening existentials

*)
let rec handling_spec env (scr_spec:normalisedStagedSpec) (h_norm:(string * disj_spec)) (h_ops:(string * string option * disj_spec) list) : spec list * fvenv = 
  let@ _ = Debug.span (fun r ->
    (* Format.asprintf "handling" *)
    debug ~at:3 ~title:"handling_spec" "match\n  (*@@ %s @@*)\nwith\n| ...\n| ...\n==>\n%s" (string_of_spec (normalisedStagedSpec2Spec scr_spec)) (string_of_result string_of_disj_spec (Option.map fst r))
    ) in
  let (scr_eff_stages, scr_normal) = scr_spec in 
  match scr_eff_stages with 
  | [] ->
    (* the scrutinee's effects have been completely handled, so go into the value case *)
    let (h_val_param, h_val_spec) = h_norm in 

    let current =
      (* Given match 1 with v -> v | effect ..., replace v with 1 in the value case *)
      let (_, _, _) = scr_normal in

      let new_res = verifier_getAfreeVar "rez" in
      (* Format.printf "new_res: %s@."  new_res; *)
      let h_spec = instantiateSpecList [h_val_param, Var new_res] h_val_spec in
      (* Format.printf "h_spec: %s@." (string_of_disj_spec h_spec); *)

      (* the heap state present in the scrutinee also carries forward *)
      let (ex, (p1, h1), (p2, h2)) = scr_normal in
      let p2 = instantiatePure ["res", Var new_res] p2 in
      (* Format.printf "p2: %s@." (string_of_pi p2); *)
      let hist = [[Exists (new_res::ex); Require (p1, h1); NormalReturn (p2, h2)]] in

      let@ _ = Debug.span (fun r ->
        debug ~at:3 ~title:"handling_spec: completely handled" "match\n  (*@@ %s @@*)\nwith\n| %s -> (*@@ %s *@@)\n| ...\n==>\n%s" (string_of_spec (normalisedStagedSpec2Spec scr_spec)) h_val_param (string_of_disj_spec h_val_spec) (string_of_result string_of_disj_spec r);
      ) in

      concatenateSpecsWithSpec hist h_spec
    in

    current, env
    
  | x :: xs ->
    (* there is an effect stage x in the scrutinee which may or may not be handled *)
    let perform_ret =
      match x.e_ret with 
      | Var ret -> ret
      | _ -> failwith "effect return is not var"
    in
    let (label, _) = x.e_constr in
    match lookforHandlingCases h_ops label with 
    | None ->

      let@ _ = Debug.span (fun r ->
        debug ~at:3 ~title:(Format.asprintf "handling_spec: unhandled effect %s" label)"%s\n==>\n%s" (string_of_spec (normalisedStagedSpec2Spec scr_spec)) (string_of_result string_of_disj_spec (Option.map fst r));
      ) in

      (* effect x is unhandled. handle the rest of the trace and append it after the unhandled effect. this assumption is sound for deep handlers, as if x is resumed, xs will be handled under this handler. *)
      let r, env = handling_spec env (xs, scr_normal) h_norm h_ops in
      let current = concatenateEventWithSpecs (effectStage2Spec [x]) (r) in


      current, env

    | Some (effFormalArg, handler_body_spec) ->
      (* effect x is handled by a branch of the form (| (Eff effFormalArg) k -> spec) *)
      (* TODO we might have to constrain this *)

      (* debug ~at:5 ~title:"before freshen" "%s" (string_of_disj_spec handler_body_spec); *)

      (* freshen, as each instance of the handler body should not interfere with previous ones *)
      let handler_body_spec = renamingexistientalVar handler_body_spec in

      (* debug ~at:5 ~title:(Format.asprintf "handler_body_spec for effect stage %s" (fst x.e_constr)) "%s" (string_of_disj_spec handler_body_spec); *)

      (* the rest of the trace is now the spec of the continuation *)
      let continuation_spec = normalisedStagedSpec2Spec (xs, scr_normal) in 

      let@ _ = Debug.span (fun r ->
        debug ~at:3 ~title:"handling_spec: handled" "match\n  (*@@ %s @@*)\nwith\n| %s k -> (*@@ %s @@*)\n| ...\n\ncontinue's spec is the scrutinee's continuation:\n  %s\n\n==>\n%s" (string_of_spec (normalisedStagedSpec2Spec scr_spec)) (fst x.e_constr) (string_of_disj_spec handler_body_spec) (string_of_spec continuation_spec) (string_of_result string_of_disj_spec (Option.map fst r));
      ) in

      let handled_spec, env =
        (* make use of the handler body spec instead of reanalyzing. for each of its disjuncts, ... *)
        handler_body_spec |> concat_map_state env (fun handler_body env ->
          let (eff_stages, norm_stage) = normalise_spec handler_body in

          (* ... each continue stage in this disjunct of the handler spec should be substituted with the spec for continue *)
          let handled, env = eff_stages |> map_state env (fun h_eff_stage env ->
            match h_eff_stage.e_constr with
            | ("continue", [cont_arg]) ->
              let cont_ret = h_eff_stage.e_ret in
 
              (* Given the following running example:

                match (let r = perform A in perform B) with
                | effect A k -> let q = continue k () in ...
                | ...

                but where the scrutinee and continue are both represented by the specs of those expressions,
              *)

              (* the spec of continue is the continuation scr[perform A] *)
              (* replace r with () in the spec of continue *)
              let cont_spec1 =
                let bindings = bindFormalNActual [perform_ret] [cont_arg] in 
                instantiateSpec bindings continuation_spec
              in

              (* only freshen after that. freshening is needed as each resumption of the continue spec results in new existentials *)
              let cont_spec2 = renamingexistientalVar [cont_spec1] in 

              debug ~at:5 ~title:"handling_spec: replace ret of effect stage with arg of continue (in continue spec)" "%s\n[%s := %s]\n==>\n%s\n==>\n%s" (string_of_spec continuation_spec) perform_ret (string_of_term cont_arg) (string_of_spec cont_spec1) (string_of_disj_spec cont_spec2);

              (* deeply (recursively) handle the rest of each continuation, to figure out the full effects of this continue. note that this is the place where we indirectly recurse on xs, by making it the spec of continue and recursing on each continue stage. this gives rise to tree recursion in a multishot setting. *)
              let handled_rest, env = 
                cont_spec2 |> concat_map_state env (fun c env ->
                  let r, env = handling_spec env (normalise_spec c) h_norm h_ops in
                  r, env)
              in

              (* add an equality between the result of continue and q above (the return term of this stage) *)
              let handled_rest1 =
                constrain_final_res handled_rest cont_ret
              in

              (* ensure heap state present in this part of the scrutinee propagates *)
              let handled_rest2 =
                let { e_evars; e_pre = (p1, h1); e_post = (p2, h2); _} = h_eff_stage in
                let existing = [Exists e_evars; Require (p1, h1); NormalReturn (p2, h2)] in
                concatenateEventWithSpecs existing handled_rest1 
              in

              debug ~at:5 ~title:"handling_spec: continue's ret = ret of handled scrutinee" "%s\n==>\n%s\n==>\n%s" (string_of_disj_spec handled_rest) (string_of_disj_spec handled_rest1) (string_of_disj_spec handled_rest2);

              (* TODO this is not needed? *)
              (* rename res *)
              (* let nv= verifier_getAfreeVar "rez" in *)
              (* let handled_rest = instantiateSpecList ["res", Var nv] handled_rest in *)

              handled_rest2, env
            | _ ->
              (* not a continue stage, so just append without doing anything *)
              let current = [normalisedStagedSpec2Spec ([h_eff_stage], freshNormalStage)] in

              (* TODO this is not needed? *)
              (* let nv= verifier_getAfreeVar "rez" in *)
              (* let current = instantiateSpecList ["res", Var nv] current in *)

              current, env)
          in
          let handled =
            match handled with
            | [] ->
              (* happens when there are handler branches without continues or other function calls/stages *)
              []
            | _ ->
              (* given the effects of each continue/stage, concat them from left to right *)
              foldl1 concatenateSpecsWithSpec handled
          in
          let norm = normalisedStagedSpec2Spec ([], norm_stage) in

          let current = concatenateSpecsWithEvent handled norm in

          current, env)
      in
      let res =
        (* after handling stage/effect x, make sure the heap state associated with it propagates, *)
        let { e_evars; e_constr = (_, arg); e_pre = (p1, h1); e_post = (p2, h2); _ } = x in
        let bindings = 
          match effFormalArg, arg with 
          | _, [] | None, _ -> [] 
          | Some e, effactualArg ::_ -> [(e, effactualArg)]
        in 
        let hist = [Exists e_evars; Require (p1, h1); NormalReturn (p2, h2)] in
        concatenateEventWithSpecs hist (instantiateSpecList bindings handled_spec), env
      in
      (* Format.printf "handling_spec =====> %s@." (string_of_disj_spec (fst res)); *)
      res


 
(** may update the environment because of higher order functions *)
let rec infer_of_expression (env:fvenv) (history:disj_spec) (expr:core_lang): disj_spec * fvenv =
  if SSet.mem "res" (used_vars_disj_spec history) then
    failwith (Format.asprintf "invariant violated: { %s } %s is not res-free" (string_of_disj_spec history) (string_of_core_lang expr));
  (* TODO infer_of_expression is likely O(n^2) due to appending at the end *)
  let res, env =
    match expr with
    | CValue v -> 
      let event = NormalReturn (res_eq v, EmptyHeap) in 
      concatenateSpecsWithEvent history [event], env

    | CLet (str, expr1, expr2) ->
      let phi1, env = infer_of_expression env history expr1 in 

      let phi2, env = infer_of_expression env [freshNormalReturnSpec] expr2 in

          (* let phi2, env, _lambdas_in_expr2 =
            let ll =
              let prev = SMap.bindings env.fv_lambda |> List.map fst |> SSet.of_list in
              let curr = SMap.bindings env1.fv_lambda |> List.map fst |> SSet.of_list in
              SSet.diff curr prev
            in
            phi2, env1, ll
          in *)

      (* preserve invariant that left side is res-free *)
      phi1 |> concat_map_state env (fun spec env -> 
        (* Format.printf "lang %s@." (string_of_core_lang expr1); *)
        (* Format.printf "spec %s@." (string_of_spec spec); *)
        (* let retN = retrieve_return_value spec in 
        match retN with 
        | UNIT ->
          infer_of_expression env [spec] expr2
        (*| Var freshV -> 
          if String.compare str "_" == 0 then infer_of_expression env [spec] expr2
          
          else if String.compare str "i" == 0 || String.compare str "j" == 0  then 
            (
            (*print_endline ("replacing " ^ freshV ^ " with " ^str);
            print_endline ("spec   " ^ string_of_spec spec);*)
            (* instantiate the exist value first *)
            let bindings = bindNewNames [freshV] [str] in 
            let spec' = instantiateExistientalVarSpec spec bindings in 
            (*print_endline ("spec'  " ^ string_of_spec spec');*)
            (* instantiate the terms value first *)
            let bindings = bindFormalNActual [freshV] [Var str] in 
            let spec' = instantiateSpec bindings spec' in 
            (*print_endline ("spec'' " ^ string_of_spec spec'); *)
            (*let spec' = removeExist [spec'] freshV in *)
            infer_of_expression env [spec'] expr2)
          
          else 
            let bindings = bindFormalNActual [str] [retN] in 
            let phi2 = infer_of_expression env [spec] expr2 in 
            instantiateSpecList bindings phi2
            *)
        | _ when String.equal str "_" ->
          infer_of_expression env [spec] expr2
        | _ -> *)


          (* rather than create an existential, we substitute the new variable away *)
          (* let bindings = bindFormalNActual [str] [retN] in  *)
          (* can't do this because we can't reliably get a res *)

          (* the return value is context-sensitive and depends on what in the history came before *)
          let ret =
            match split_last spec with
            | _, RaisingEff (_pre, _post, _constr, Var ret) -> ret
            | _, HigherOrder (_pre, _post, _constr, Var ret) -> ret
            | _, RaisingEff (_, _, _, ret) | _, HigherOrder (_, _, _, ret) -> failwith (Format.asprintf "ret not a variable: %s" (string_of_term ret))
            | _ -> "res"
          in

          (* create an existential by creating a fresh variable, and preserve the invariant by removing res from the post of the first expr, as it will now appear on the left of the second premise *)
          let nv = verifier_getAfreeVar "let" in
          let spec = instantiateSpec [ret, Var nv] spec in
          (* let spec = spec @ [NormalReturn (Atomic (EQ, Var nv, Var str), EmptyHeap)] in *)
          let spec = (Exists [nv]) :: spec in

          (* let var = verifier_getAfreeVar "let" in *)
          let phi2 = instantiateSpecList [str, Var nv] phi2 in

          concatenateSpecsWithSpec [spec] phi2, env
          (* if expr1 is a lambda, copy its binding to the method env before processing expr2 *)
          (* let env =
            match phi1 with
            | [p] ->
              (match retrieve_return_value p with
              | TLambda (n, _params, _sp) ->
                let lspec = SMap.find n env.fv_lambda in
                (* rename, so created predicate will match *)
                let lspec = { lspec with m_name = str } in
                { env with fv_methods = env.fv_methods |> SMap.add str lspec;
                  fv_lambda_names = (n, str) :: env.fv_lambda_names }
              | _ -> env)
            | _ -> env
          in *)

          (* Here, we only instantiate the expr2 and *)
          (* let phi2' = instantiateSpecList bindings phi2 in *)
          (* let phi2' = phi2 in *)

          (* also substitute inside the specs of lambdas defined in expr2. this has to be done after expr2 is inferred (as then we will know which lambda specs to change), so we need to fix all methods which lambdas have been bound to as well *)
          (* let env =
            let fv_lambda =
              env.fv_lambda |> SMap.mapi (fun k v -> if SSet.mem k lambdas_in_expr2 then { v with m_spec = Option.map (fun s -> instantiateSpecList bindings s) v.m_spec } else v)
            in
            let fv_methods =
              let methods_to_change =
                env.fv_lambda_names |> List.filter_map (fun (n, m) -> if SSet.mem n lambdas_in_expr2 then Some m else None) |> SSet.of_list
              in
              SMap.mapi (fun k v -> if SSet.mem k methods_to_change then { v with m_spec = Option.map (fun s -> instantiateSpecList bindings s) v.m_spec } else v) env.fv_methods
            in
            { env with fv_lambda; fv_methods }
          in *)

          (* concat spec -- the spec for expr 1 -- in front *)
          (* concatenateSpecsWithSpec [spec] phi2', env *)

        )
    | CRef v -> 
      let freshVar = verifier_getAfreeVar "ref" in 
      let event = NormalReturn (res_eq (Var freshVar), PointsTo(freshVar, v)) in 
      concatenateSpecsWithEvent history [Exists [freshVar];event], env


    | CRead str -> 
      let freshVar = verifier_getAfreeVar str in 
      let event = [Exists [freshVar];Require(True, PointsTo(str, Var freshVar)); 
        NormalReturn (res_eq (Var freshVar), PointsTo(str, Var freshVar))] in 
      concatenateSpecsWithEvent history event, env


    | CAssert (p, h) -> 
      let temp = concatenateSpecsWithEvent history [Require(p, h)] in 
      concatenateSpecsWithEvent temp [(NormalReturn(And (res_eq UNIT, p), h))], env

    | CPerform (label, arg) -> 
          
      let arg = 
        match arg with 
        | Some v -> [v]
        | _ -> []
      in 
      let freshVar = verifier_getAfreeVar "per" in 
      (* after adding the perfome stage, we need to add a normal return. *)
      concatenateSpecsWithEvent history 
      [Exists [freshVar];RaisingEff(True, EmptyHeap, (label,arg), Var freshVar);
      NormalReturn (res_eq (Var freshVar), EmptyHeap)], env


    | CResume v ->  
      let f = verifier_getAfreeVar "re" in
      let res =
        concatenateSpecsWithEvent history [Exists [f]; RaisingEff (True, EmptyHeap, ("continue", [v]), Var f)]
      in
      res, env
    | CFunCall (fname, actualArgs) -> 
      (match List.mem fname primitives with
      | true ->
        (match fname, actualArgs with
        | "+", [x1; x2] ->
          let event = NormalReturn (res_eq (Plus(x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent history [event], env
        | "-", [x1; x2] ->
          let event = NormalReturn (res_eq (Minus(x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent history [event], env
        | "=", [x1; x2] ->
          (* let event = NormalReturn (Atomic (EQ, x1, x2), EmptyHeap, Eq (x1, x2)) in *)
          let event = NormalReturn (res_eq (Rel (EQ, x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent history [event], env
        | "not", [x1] ->
          let event = NormalReturn (res_eq (TNot (x1)), EmptyHeap) in
          concatenateSpecsWithEvent history [event], env
        | "&&", [x1; x2] ->
          let event = NormalReturn (res_eq (TAnd (x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent history [event], env
        | "||", [x1; x2] ->
          let event = NormalReturn (res_eq (TOr (x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent history [event], env
        | ">", [x1; x2] ->
          let event = NormalReturn (res_eq (Rel (GT, x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent history [event], env
        | "<", [x1; x2] ->
          let event = NormalReturn (res_eq (Rel (LT, x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent history [event], env
        | ">=", [x1; x2] ->
          let event = NormalReturn (res_eq (Rel (GTEQ, x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent history [event], env
        | "<=", [x1; x2] ->
          let event = NormalReturn (res_eq (Rel (LTEQ, x1, x2)), EmptyHeap) in
          concatenateSpecsWithEvent history [event], env
        | "::", [x1; x2] ->
          let event = NormalReturn (res_eq (TApp ("cons", [x1; x2])), EmptyHeap) in
          concatenateSpecsWithEvent history [event], env
        | _ -> failwith (Format.asprintf "unknown primitive: %s, args: %s" fname (string_of_list string_of_term actualArgs)))
      | false ->
        let spec_of_fname =
          (match retrieveSpecFromEnv fname env with 
          | None ->
            let ret = verifier_getAfreeVar "ret" in
            [[Exists [ret]; HigherOrder (True, EmptyHeap, (fname, actualArgs), Var ret)]]
          | Some (formalArgs, spec_of_fname) -> 
            (* TODO should we keep existentials? *)
            let spec = renamingexistientalVar spec_of_fname in
            (* let spec = freshen spec_of_fname in *)
            (* Format.printf "after freshen: %s@." (string_of_disj_spec spec); *)
            if List.compare_lengths formalArgs actualArgs <> 0 then
              failwith (Format.asprintf "too few args. formals: %s, actual: %s@." (string_of_list Fun.id formalArgs) (string_of_list string_of_term actualArgs));
            let spec =
              (* we've encountered a function call, e.g. f x y.
                we look up the spec for f. say it looks like:
                  let f g h (*@ g$(...); ... @*) = ...
                we now want to instantiate g with the spec for x. *)
              let fnArgs = List.map2 (fun p x ->
                match x with
                | Var a ->
                  (p, retrieveSpecFromEnv a env)
                | TLambda _ ->
                  (* if a is a lambda, get its spec here *)
                  failwith "lambda case not implemented"
                | _ -> (p, None)
                ) formalArgs actualArgs
              in
              (* fnArgs is a map of g -> spec, h -> none, assuming h is not a functino *)
              instantiate_higher_order_functions fname fnArgs spec
            in
            (* Format.printf "after ho fns: %s@." (string_of_disj_spec spec); *)
            let bindings = bindFormalNActual (formalArgs) (actualArgs) in 
            let instantiatedSpec = instantiateSpecList bindings spec in 
            instantiatedSpec)
            (*print_endline ("====\n"^ string_of_spec_list spec_of_fname);*)
        in
        let _spec_of_fname =
          (* this is an alternative implementation for this whole case, which simply generates an uninterpreted function and lets the entailment procedure take care of unfolding (since the implementation above can be seen as unfolding once). unfortunately the handler reasoning in the effects work relies on unfolding in the forward reasoning, so we can't switch to it yet, but this implementation should work for higher-order *)
          let ret = verifier_getAfreeVar "ret" in
          [[Exists [ret]; HigherOrder (True, EmptyHeap, (fname, actualArgs), Var ret); NormalReturn (res_eq (Var ret), EmptyHeap)]]
        in
        concatenateSpecsWithSpec history spec_of_fname, env)
    | CWrite  (str, v) -> 
      let freshVar = verifier_getAfreeVar "wr" in 
      let event = [Exists [freshVar];Require(True, PointsTo(str, Var freshVar)); 
                    NormalReturn (res_eq UNIT, PointsTo(str, v))] in 
      concatenateSpecsWithEvent history event, env


    | CIfELse (v, expr2, expr3) -> 
      let eventThen = NormalReturn (Atomic (EQ, v, TTrue), EmptyHeap) in 
      let eventElse = NormalReturn (Not (Atomic (EQ, v, TTrue)), EmptyHeap) in 
      let currentThen = concatenateSpecsWithEvent history [eventThen] in 
      let currentElse = concatenateSpecsWithEvent history [eventElse] in 
      let r1, env = infer_of_expression env currentThen expr2 in
      let r2, env = infer_of_expression env currentElse expr3 in
      r1 @ r2, env


    | CLambda (params, given_spec, body) ->
      let inferred, env = infer_of_expression env [[]] body in
      let inferred = inferred |> List.map (fun s -> s |> normalise_spec |> normalisedStagedSpec2Spec) in
      let lid = verifier_getAfreeVar "lambda" in
      debug ~at:2 ~title:(Format.asprintf "lambda spec %s" lid) "%s" (string_of_disj_spec inferred);
      let mdef = {
        m_name = lid;
        m_params = params; (* TODO unit param? *)
        m_spec = Some inferred; (* TODO given? *)
        m_body = body;
        m_tactics = [];
      } in
      let env = { env with fv_lambda = SMap.add lid mdef env.fv_lambda } in
      let env =
        match given_spec with
        | None -> env
        | Some g -> { env with fv_lambda_obl = (inferred, g) :: env.fv_lambda_obl }
      in
      (* TODO given *)
      let event = NormalReturn (res_eq (TLambda (lid, params, inferred)), EmptyHeap) in 
      concatenateSpecsWithEvent history [event], env

    | CMatch (scr, Some val_case, eff_cases, []) -> (* effects *)
      (* infer specs for branches of the form (Constr param -> spec), which also updates the env with obligations *)
      let inferred_branch_specs, env =
        List.fold_right (fun (effname, param, spec, body) (t, env) ->
          let r, env = infer_of_expression env [[]] body in
          let env, sp =
            match spec with
            | None -> env, r
            | Some s -> { env with fv_match_obl = (r, s) :: env.fv_match_obl }, s
          in
          (effname, param, sp) :: t, env
        ) eff_cases ([], env)
      in
      let inferred_val_case, env =
        let (param, body)  = val_case in
        let inf_val_spec, env = infer_of_expression env [[]] body in
        (param, inf_val_spec), env
      in
      (* for each disjunct of the scrutinee's behaviour, reason using the handler *)
      let phi1, env = infer_of_expression env [freshNormalReturnSpec] scr in 
      let afterHandling, env =
        concat_map_state env (fun spec env -> 
          handling_spec env (normalise_spec spec) inferred_val_case inferred_branch_specs
        ) phi1
      in 
      let res, env = concatenateSpecsWithSpec history afterHandling, env in
      res, env
    | CMatch (discr, None, _, cases) -> (* pattern matching *)
      (* this is quite similar to if-else. generate a disjunct for each branch with variables bound to the result of destructuring *)
      let dsp, env = infer_of_expression env history discr in
      let dsp, env = dsp |> concat_map_state env (fun sp env ->
        let ret = retrieve_return_value sp in
        cases |> concat_map_state env (fun (constr, vars, body) env -> 
          (* TODO this is hardcoded for lists for now *)
          match constr, vars with
          | "[]", [] ->
            let nil_case =
              let c = conj [Atomic (EQ, TApp ("is_nil", [ret]), TTrue)] in
              [NormalReturn (c, EmptyHeap)]
            in 
            infer_of_expression env (concatenateSpecsWithEvent history nil_case) body
          | "::", [v1; v2] ->
            let cons_case =
              let c = conj [
                Atomic (EQ, TApp ("is_cons", [ret]), TTrue);
                Atomic (EQ, TApp ("head", [ret]), Var v1);
                Atomic (EQ, TApp ("tail", [ret]), Var v2);
              ] in
              [Exists [v1; v2]; NormalReturn (c, EmptyHeap)]
            in
            infer_of_expression env (concatenateSpecsWithEvent history cons_case) body
          | _ -> failwith (Format.asprintf "unknown constructor: %s" constr)))
      in
      dsp, env
    | CMatch (_, Some _, _, _ :: _) ->
      (* TODO *)
      failwith "combining effect handlers and pattern matching not yet unimplemented"
  in
  debug ~at:2 ~title:"forward rules" "{%s}\n%s\n{%s}" (string_of_disj_spec history) (string_of_core_lang expr) (string_of_disj_spec res);
  res, env
