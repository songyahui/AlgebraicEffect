

open Hipprover
open Hipcore
module Pretty = Pretty
module ProversEx = ProversEx
module Debug = Debug
module Common = Hiptypes
open Ocamlfrontend
open Parsetree
open Asttypes
(* get rid of the alias *)
type string = label
(* open Rewriting *)
open Pretty
open Debug
open Hiptypes
open Normalize

let file_mode = ref false
let test_mode = ref false
let tests_failed = ref false

let rec input_lines file =
  match try [input_line file] with End_of_file -> [] with
   [] -> []
  | [line] -> (String.trim line) :: input_lines file
  | _ -> failwith "Weird input_line return value"
;;



let rec shaffleZIP li1 li2 = 
  let rec aux a li = 
    match li with 
    | []-> []
    | y :: ys -> (a, y) :: (aux a ys)
  in 
  match li1 with 
  | [] -> []
  | x ::xs -> List.append (aux x li2) (shaffleZIP xs li2) 
;;


assert ((List.length (shaffleZIP [1;2;3] [4;5;6])) = 9 );;

(*
let string_of_effect_constructor x :string =
  match x.peff_kind with
  | Peff_decl(_, _) -> ""
      
  | _ -> ""
;;
type rec_flag = Nonrecursive | Recursive
*)

let string_of_payload p =
  match p with
  | PStr str -> Pprintast.string_of_structure str
  | PSig _ -> "sig"
  | PTyp _ -> "typ"
  | PPat _ -> "pattern"


let string_of_attribute (a:attribute) : string = 
  let name = a.attr_name.txt in 
  let payload = a.attr_payload in 
  Format.sprintf "name: %s, payload: %s" name (string_of_payload payload)

let string_of_attributes (a_l:attributes): string = 
  List.fold_left (fun acc a -> acc ^ string_of_attribute a ) "" a_l;;

let debug_string_of_core_type t =
  Format.asprintf "type %a@." Pprintast.core_type t


let rec string_of_effectList (specs:spec list):string =
  match specs with 
  | [] -> ""
  | x :: xs -> string_of_spec x ^ " /\\ "^  string_of_effectList xs 


let string_of_effectspec spec:string =
    match spec with
    | None -> "<no spec given>"
    (* | Some (pr, po) ->
      Format.sprintf "requires %s ensures %s" (string_of_spec pr) (string_of_effectList po) *)
    | Some p -> string_of_spec p


let debug_string_of_expression e =
  Format.asprintf "%a" (Printast.expression 0) e

let string_of_longident l =
  l |> Longident.flatten |> String.concat "."


let rec getIndentName (l:Longident.t): string = 
  (match l with 
        | Lident str -> str
        | Ldot (t, str) -> getIndentName t ^ "." ^ str
        | _ -> "getIndentName: dont know " ^ string_of_longident l
        )
        ;;

(* information we record after seeing a function *)
type fn_spec = {
  pre: spec;
  post: spec list;
  formals: string list;
}


(* at a given program point, this captures specs for all local bindings *)
type fn_specs = fn_spec SMap.t


(* effect Foo : int -> (int -> int) *)
type effect_def = {
  params: typ list; (* [TInt] *)
  res: typ list * typ (* ([TInt], TInt) *)
}

type env = {
  (* module name -> a bunch of function specs *)
  modules : fn_specs SMap.t;
  current : fn_specs;
  (* the stack stores higher-order functions which may produce effects.
     an entry like a -> Foo(1) means that the variable a in scope has been applied to
     the single argument 1. nothing is said about how many arguments are remaining,
     (though that can be figured out from effect_defs) *)
  effect_defs : effect_def SMap.t;
}

type function_without_spec = (string * expression * string list)
let (env_function_without_spec: ((function_without_spec list)ref)) = ref [] 

let rec retrieveFuntionWithoutSpecDefinition str li = 
  match li with 
  | [] ->  None 
  | (s, b, f) :: xs  -> if String.compare s str == 0 then (Some (s, b, f)) 
  else retrieveFuntionWithoutSpecDefinition str xs 


let rec string_of_basic_v li: string = 
  match li with 
  | [] -> ""
  | (str, bt) :: xs ->(str ^ "=" ^ string_of_term bt  ^ ", ") ^ string_of_basic_v xs 


module Env = struct
  let empty = {
    modules = SMap.empty;
    current = SMap.empty;
    effect_defs = SMap.empty
  }

  let add_fn f spec env =
    { env with current = SMap.add f spec env.current }

  let add_effect name def env =
    { env with effect_defs = SMap.add name def env.effect_defs }

  let find_fn f env =
    SMap.find_opt f env.current
  
  
  let find_effect_arg_length name env =
    match SMap.find_opt name env.effect_defs with 
    | None -> None 
    | Some def -> 
      let n1 = List.length (def.params)  in 
      let (a, _) = def.res in 
      let n2 = List.length a in 
      Some (n1 + n2)


  let add_module name menv env =
    { env with modules = SMap.add name menv.current env.modules }

  (* dump all the bindings for a given module into the current environment *)
  let open_module name env =
    let m = SMap.find name env.modules in
    let fns = SMap.bindings m |> List.to_seq in
    { env with current = SMap.add_seq fns env.current }
end




let string_of_fn_specs specs =
  Format.sprintf "{%s}"
    (SMap.bindings specs
    |> List.map (fun (n, s) ->
      Format.sprintf "%s -> %s/%s/%s" n
        (string_of_spec s.pre)
        (string_of_spec (List.hd s.post))
        (s.formals |> String.concat ","))
    |> String.concat "; ")

let string_of_env env =
  Format.sprintf "%s\n%s"
    (env.current |> string_of_fn_specs)
    (env.modules
      |> SMap.bindings
      |> List.map (fun (n, s) -> Format.sprintf "%s: %s" n (string_of_fn_specs s))
      |> String.concat "\n")



type experiemntal_data = (float list * float list) 


(* let entailmentHeapAssertion k1 pi : bool = 
  let (re, _) = check_pure (kappaToPure k1) pi in re *)

let rec lookUpFromPure p str : term option = 
  match p with 
  | True -> None 
  | False -> None 
  | Atomic (EQ, Var name , Num i) -> 
    if String.compare str name == 0 then Some (Num i)
    else None 

  | And   (p1, p2) -> 
    (match lookUpFromPure p1 str with 
    | None -> lookUpFromPure p2 str
    | Some n -> Some n 
    )
  | Atomic _
  | Or    _
  | Imply  _
  | Not   _
  | Subsumption _
  | Predicate _ -> None (*raise (Foo "lookUpFromPure error")*)









open Forward_rules


let mergePredicates (preds:((string * term list ) list)) (slps:sl_pred_def SMap.t) : (string list * pi * kappa) = 
  
  List.fold_left (fun (accEx, accPi, accHeap) (str, actualArg) -> 
    try 
      let ({p_sl_ex; p_sl_name; p_sl_params; p_sl_body}:sl_pred_def)  = SMap.find str slps in 
      assert (String.compare p_sl_name str == 0);
      let (p_sl_ex, p_sl_body) = renamingexistientalVarState p_sl_ex p_sl_body in 
      let bindings = bindFormalNActual (p_sl_params) (actualArg) in 
      let (pi, kappa) = p_sl_body in 
      let p_sl_body' = (instantiatePure bindings pi, instantiateHeap bindings kappa) in 
      let (pNew, heapNew) = p_sl_body' in 
      (p_sl_ex@accEx, And(accPi, pNew), SepConj(accHeap, heapNew))

    with 
      | Not_found -> 
        raise (Failure (str ^ " not found"))
  ) ([], True, EmptyHeap) preds


let rec decomposeStateForPredicate p : (((string * term list ) list) * pi) =
    match p with 
    | Predicate (str, actualArg) -> ([(str, actualArg)], True)
    | And   (p1, p2) -> 
      (*print_endline ("AND!   " ^ string_of_pi p1 ^ ",   " ^ string_of_pi p2);*)
      let (pred1, pi1) = decomposeStateForPredicate p1 in 
      let (pred2, pi2) = decomposeStateForPredicate p2 in 
      (pred1@pred2, (And (pi1, pi2)))

    | Atomic _
    | Subsumption _
    | True
    | Not _
    | False -> ([], p)
    | Or    _
    | Imply  _ -> failwith "decomposePredicate nor and or and imply"





let replaceSLPredicatesWithDef (specs:disj_spec) (slps:sl_pred_def SMap.t) = 
  let helper (stage:stagedSpec): spec = 
    match stage with 
    | Require (p, h) ->
      let (preds, p') = decomposeStateForPredicate p in 
      let (ex, p_pred, h_pred) = mergePredicates preds slps in 
      [Exists ex; Require (p_pred, h_pred); Require (p', h)]

    | HigherOrder (p, h, (f, args), ret) ->
      let (preds, p') = decomposeStateForPredicate p in 
      let (ex, p_pred, h_pred) = mergePredicates preds slps in 
      [Exists ex; NormalReturn (p_pred, h_pred);  HigherOrder (p', h, (f, args), ret)]

    | NormalReturn (p, heap) ->
      let (preds, p') = decomposeStateForPredicate p in 
      let (ex, p_pred, h_pred) = mergePredicates preds slps in 
      [Exists ex; NormalReturn (p_pred, h_pred);  NormalReturn (p', heap)]

    | RaisingEff (p, h, (f, args), ret) ->
      let (preds, p') = decomposeStateForPredicate p in 
      let (ex, p_pred, h_pred) = mergePredicates preds slps in 
      [Exists ex; NormalReturn (p_pred, h_pred);  RaisingEff (p', h, (f, args), ret)]

    | Exists _ | TryCatch _ -> [stage]
  in 
  normalise_spec_list
  (List.map (fun spec ->     
    List.flatten(List.map (fun stage -> helper stage) spec )
  ) specs)
  

let retrieveSpecFromMs_Ps (fname: string) (ms:meth_def list) (ps:pred_def SMap.t) : (string list * spec list) option = 
  match 
  SMap.find_opt fname ps
  |> Option.map (fun p -> (p.p_params, p.p_body))

  with 
  | Some res -> Some res
  | None -> 

  let (>>=) = Option.bind in
  SMap.find_opt fname 
    (ms |> List.map (fun m -> m.m_name, m)
    |> List.to_seq
    |> SMap.of_seq)
  >>= (fun m -> Option.map (fun sp -> (m.m_params, sp)) m.m_spec)



let replacePredicatesWithDef (specs:disj_spec) (ms:meth_def list) (ps:pred_def SMap.t) : disj_spec = 
  let rec helper (spec:spec) : disj_spec = 
    match spec with 
    | [] -> [[]]
    | HigherOrder (pi, h, (f, actualArg), ret) :: xs  -> 
      (match retrieveSpecFromMs_Ps f ms ps with 
      | None -> let temp = helper xs in 
                List.map (fun li -> HigherOrder (pi, h, (f, actualArg), ret) :: li) temp

      | Some (p_params, p_body) -> 
      (*print_endline ("\n replacePredicates for " ^ p_name);
      print_endline ("p_params: " ^ (List.map (fun a-> a) p_params |> String.concat ", "));
      print_endline ("actualArg: " ^ (List.map (fun a-> string_of_term a) actualArg |> String.concat ", "));


      print_endline ("ret = " ^ string_of_term ret);
      *)

      let bindings = bindFormalNActual (p_params) (actualArg) in 

      (*print_endline (string_of_disj_spec p_body);*)
      let p_body = renamingexistientalVar p_body in 
      (*print_endline (" ===> " ^ string_of_disj_spec p_body);*)

      let p_body' =  (instantiateSpecList bindings p_body)  in 




      let p_body' = normalise_spec_list (List.map (fun a ->
              let returnTerm = 
                match retriveLastRes a with 
                | Some (Var t) -> t 
                | Some t -> 
                  print_endline (string_of_term t);
                  failwith "there was a res term but not a variable"
                | None -> 
                  failwith "there is no res value"
              in 
              instantiateSpec [(returnTerm, ret)] a
            )
            p_body' )
      in 
      let temp = helper xs in 
      List.flatten (List.map (fun li -> 
        List.map (
          fun p_b -> 
            NormalReturn(pi, h) ::p_b  @ li
        ) p_body'
      ) temp)

      )


      



    | x :: xs  -> 
      let temp = helper xs in 
      List.map (fun li -> x :: li) temp



  
  in  List.flatten (List.map (fun spec -> helper spec) specs)

let string_of_token =
  let open Parser in
  function
| AMPERAMPER -> "AMPERAMPER"
| AMPERSAND -> "AMPERSAND"
| AND -> "AND"
| AS -> "AS"
| ASSERT -> "ASSERT"
| BACKQUOTE -> "BACKQUOTE"
| BANG -> "BANG"
| BAR -> "BAR"
| BARBAR -> "BARBAR"
| BARRBRACKET -> "BARRBRACKET"
| BEGIN -> "BEGIN"
| CHAR _ -> "CHAR"
| CLASS -> "CLASS"
| COLON -> "COLON"
| COLONCOLON -> "COLONCOLON"
| COLONEQUAL -> "COLONEQUAL"
| COLONGREATER -> "COLONGREATER"
| COMMA -> "COMMA"
| CONSTRAINT -> "CONSTRAINT"
| DO -> "DO"
| DONE -> "DONE"
| DOT -> "DOT"
| DOTDOT -> "DOTDOT"
| DOWNTO -> "DOWNTO"
| EFFECT -> "EFFECT"
| EXISTS -> "EXISTS"
| ELSE -> "ELSE"
| END -> "END"
| EOF -> "EOF"
| EQUAL -> "EQUAL"
| EXCEPTION -> "EXCEPTION"
| EXTERNAL -> "EXTERNAL"
| FALSE -> "FALSE"
| FLOAT _ -> "FLOAT"
| FOR -> "FOR"
| FUN -> "FUN"
| FUNCTION -> "FUNCTION"
| FUNCTOR -> "FUNCTOR"
| REQUIRES -> "REQUIRES"
| ENSURES -> "ENSURES"
| EMP -> "EMP"
| GREATER -> "GREATER"
| GREATERRBRACE -> "GREATERRBRACE"
| GREATERRBRACKET -> "GREATERRBRACKET"
| IF -> "IF"
| IN -> "IN"
| INCLUDE -> "INCLUDE"
| INFIXOP0 _ -> "INFIXOP0"
| INFIXOP1 _ -> "INFIXOP1"
| INFIXOP2 _ -> "INFIXOP2"
| INFIXOP3 _ -> "INFIXOP3"
| INFIXOP4 _ -> "INFIXOP4"
| DOTOP _ -> "DOTOP"
| LETOP _ -> "LETOP"
| ANDOP _ -> "ANDOP"
| INHERIT -> "INHERIT"
| INITIALIZER -> "INITIALIZER"
| INT _ -> "INT"
| LABEL _ -> "LABEL"
| LAZY -> "LAZY"
| LBRACE -> "LBRACE"
| LBRACELESS -> "LBRACELESS"
| LBRACKET -> "LBRACKET"
| LBRACKETBAR -> "LBRACKETBAR"
| LBRACKETLESS -> "LBRACKETLESS"
| LBRACKETGREATER -> "LBRACKETGREATER"
| LBRACKETPERCENT -> "LBRACKETPERCENT"
| LBRACKETPERCENTPERCENT -> "LBRACKETPERCENTPERCENT"
| LESS -> "LESS"
| LESSMINUS -> "LESSMINUS"
| LET -> "LET"
| LIDENT _ -> "LIDENT"
| LPAREN -> "LPAREN"
| LBRACKETAT -> "LBRACKETAT"
| LBRACKETATAT -> "LBRACKETATAT"
| LBRACKETATATAT -> "LBRACKETATATAT"
| MATCH -> "MATCH"
| METHOD -> "METHOD"
| MINUS -> "MINUS"
| MINUSDOT -> "MINUSDOT"
| MINUSGREATER -> "MINUSGREATER"
| MODULE -> "MODULE"
| MUTABLE -> "MUTABLE"
| NEW -> "NEW"
| NONREC -> "NONREC"
| OBJECT -> "OBJECT"
| OF -> "OF"
| OPEN -> "OPEN"
| OPTLABEL _ -> "OPTLABEL"
| OR -> "OR"
| PERCENT -> "PERCENT"
| PLUS -> "PLUS"
| PLUSDOT -> "PLUSDOT"
| PLUSEQ -> "PLUSEQ"
| PREFIXOP _ -> "PREFIXOP"
| PRIVATE -> "PRIVATE"
| QUESTION -> "QUESTION"
| QUOTE -> "QUOTE"
| RBRACE -> "RBRACE"
| RBRACKET -> "RBRACKET"
| REC -> "REC"
| RPAREN -> "RPAREN"
| SEMI -> "SEMI"
| SEMISEMI -> "SEMISEMI"
| HASH -> "HASH"
| HASHOP _ -> "HASHOP"
| SIG -> "SIG"
| STAR -> "STAR"
| STRING _ -> "STRING"
| STRUCT -> "STRUCT"
| THEN -> "THEN"
| TILDE -> "TILDE"
| TO -> "TO"
| TRUE -> "TRUE"
| TRY -> "TRY"
| TYPE -> "TYPE"
| UIDENT _ -> "UIDENT"
| UNDERSCORE -> "UNDERSCORE"
| VAL -> "VAL"
| VIRTUAL -> "VIRTUAL"
| WHEN -> "WHEN"
| WHILE -> "WHILE"
| WITH -> "WITH"
| COMMENT _ -> "COMMENT"
| LSPECCOMMENT -> "LSPECCOMMENT"
| RSPECCOMMENT -> "RSPECCOMMENT"
| PREDICATE -> "PREDICATE"
| LEMMA -> "LEMMA"
(* | PURE -> "PURE" *)
| DOCSTRING _ -> "DOCSTRING"
| EOL -> "EOL"
| QUOTED_STRING_EXPR _ -> "QUOTED_STRING_EXPR"
| QUOTED_STRING_ITEM _ -> "QUOTED_STRING_ITEM"
| CONJUNCTION -> "CONJUNCTION"
| DISJUNCTION -> "DISJUNCTION"
(* | IMPLICATION -> "IMPLICATION" *)
| LONG_IMPLICATION -> "LONG_IMPLICATION"
| SUBSUMES -> "SUBSUMES"
| EFFTRY -> "EFFTRY"
| EFFCATCH -> "EFFCATCH"
| PROP_TRUE -> "PROP_TRUE"
| PROP_FALSE -> "PROP_FALSE"


let debug_tokens str =
  let lb = Lexing.from_string str in
  let rec loop tokens =
    let tok = Lexer.token lb in
    match tok with
    | EOF -> List.rev (tok :: tokens)
    | _ -> loop (tok :: tokens)
  in
  let tokens = loop [] in
  let s = tokens |> List.map string_of_token |> String.concat " " in
  debug ~at:3 ~title:"debug tokens" "%s" s

let (exGlobal:(string list) ref) =  ref []
let (unifyGlobal: pi ref) = ref True  

let term_is_Extiatential t ctx =
  match t with 
  | Var str -> if existStr str ctx then true else false 
  | _ -> false 

let normaliseKappa k = 
  match k with 
  | SepConj ( sp1, EmptyHeap) -> sp1 
  | SepConj ( EmptyHeap, sp2) -> sp2  
  | _ -> k 

let rec speration_logic_ential (p1, h1) (p2, h2) : (bool) = 
(*print_endline (string_of_state (p1, h1) ^" ==> "^  string_of_state (p2, h2)); *)
let h1 = normaliseKappa h1 in 
let h2 = normaliseKappa h2 in 
let res = 
  match (h1, h2) with 
  | (_, EmptyHeap) -> true
  | (EmptyHeap, _) -> false
  | (PointsTo (v1, t1), PointsTo (v2, t2)) -> 
    if existStr v2 !exGlobal && stricTcompareTerm t1 t2 then 
      let () = unifyGlobal := And (!unifyGlobal, And (Atomic(EQ, Var v1, Var v2), p1)) in 
      (*print_string ("adding " ^ string_of_pi (And (Atomic(EQ, Var v1, Var v2), p1)) ^ "\n");*)
      true
    else if existStr v2 !exGlobal then 
      if term_is_Extiatential t2 !exGlobal then 
        let () = unifyGlobal := And (!unifyGlobal, And (Atomic(EQ, t1, t2), p1)) in 
        (*print_string ("adding " ^ string_of_pi (And (Atomic(EQ, t1, t2), p1)) ^ "\n");*)
        true
      else 
      let () = unifyGlobal := And (!unifyGlobal, And (Atomic(EQ, Var v1, Var v2), p1)) in 
      (*print_string ("adding " ^ string_of_pi (And (Atomic(EQ, Var v1, Var v2), p1)) ^ "\n");*)
      let lhs = (And(p1,  Atomic(EQ, Var v1, t1) )) in 
      let rhs = (And(p2,  Atomic(EQ, Var v2, t2) )) in 
      (*print_endline ( "yoyo1\n");
      print_endline (string_of_pi (!unifyGlobal));*)
      (ProversEx.is_valid (And(lhs, !unifyGlobal)) rhs)

    else 
      (match (t2) with 
      | Var t2Str -> 
        if existStr t2Str !exGlobal then 
          let () = unifyGlobal := And (!unifyGlobal, And (Atomic(EQ, t1, t2), p1)) in 
          (*print_string ("adding " ^ string_of_pi (And (Atomic(EQ, t1, t2), p1)) ^ "\n");*)
          true
        else 
          let lhs = (And(p1,  Atomic(EQ, Var v1, t1) )) in 
          let rhs = (And(p2,  Atomic(EQ, Var v2, t2) )) in 
          (ProversEx.is_valid (And(lhs, !unifyGlobal)) rhs)
      | _ -> 
      let lhs = (And(p1,  Atomic(EQ, Var v1, t1) )) in 
      let rhs = (And(p2,  Atomic(EQ, Var v2, t2) )) in 
      (ProversEx.is_valid (And(lhs, !unifyGlobal)) rhs))

  | (SepConj ( sp1, sp2), SepConj ( sp3, sp4)) -> 
    speration_logic_ential (p1, sp1) (p2, sp3) && speration_logic_ential (p1, sp2) (p2, sp4)
      
  | _ -> failwith ("not supporting other heap")
in (*print_string (string_of_bool res ^ "\n\n");*) res



let checkEntailmentForNormalFlow (lhs:normalStage) (rhs:normalStage) : bool = 
  let (ex1, (pi1, heap1), (pi2, heap2)) = lhs in 
  let (ex2, (pi3, heap3), (pi4, heap4)) = rhs in  
  let () = exGlobal := !exGlobal @ ex1 @ ex2 in 
  let (contravariant) = speration_logic_ential (pi3, heap3) (pi1, heap1) in 
  let (covariant)     = speration_logic_ential (pi2, heap2) (pi4, heap4) in 
  covariant && contravariant


let rec compareEffectArgument unification v1 v2 =  
  match (v1, v2) with 
  | ([], []) -> true 
  | (x::xs, y::ys) -> 
    let r1 = ProversEx.is_valid unification (Atomic(EQ, x, y)) in 
    r1 && (compareEffectArgument unification xs ys)
  | (_, _) -> false 

let checkEntailMentForEffFlow (lhs:effectStage) (rhs:effectStage) : (bool) = 
  let {e_evars=ex1; e_pre=(pi1, heap1); e_post=(pi2, heap2); e_constr=(eff1, v1); e_ret=r1; _} = lhs in 
  let {e_evars=ex2; e_pre=(pi3, heap3); e_post=(pi4, heap4); e_constr=(eff2, v2); e_ret=r2; _} = rhs in  
  let () = exGlobal := !exGlobal @ ex1 @ ex2 in 
  let (contravariant) = speration_logic_ential (pi3, heap3) (pi1, heap1) in 
  let (covariant)     = speration_logic_ential (pi2, heap2) (pi4, heap4) in 
  let effectName    = String.compare eff1 eff2 == 0  in 
  let effArgument   = compareEffectArgument !unifyGlobal v1 v2 in 
  let () =  unifyGlobal := And (!unifyGlobal, (Atomic(EQ, r1, r2))) in 
  (covariant && contravariant && effectName && effArgument) 

let rec entailmentchecking_aux (lhs:normalisedStagedSpec) (rhs:normalisedStagedSpec) : (bool) = 
  (*print_endline (string_of_pi (!unifyGlobal));
  print_endline (string_of_normalisedStagedSpec lhs ^" |===> "^ string_of_normalisedStagedSpec rhs);
  *)
  let (effSLHS, normalSLHS)  =  lhs  in 
  let (effSRHS, normalSRHS)  =  rhs  in 
  match (effSLHS, effSRHS) with 
  | ([], []) -> checkEntailmentForNormalFlow normalSLHS normalSRHS 
  | (EffHOStage x::xs, EffHOStage y::ys) -> 
    let (r1) = checkEntailMentForEffFlow x y in 
    let r2 = entailmentchecking_aux (xs, normalSLHS) (ys, normalSRHS) in 
    r1 && r2
  | (_, _) -> false 


let rec entailmentchecking_helper (lhs:normalisedStagedSpec) (rhs:normalisedStagedSpec list) : (bool) =
  match rhs with 
  | [] -> false 
  | y::ys -> 

    let () = exGlobal := [] in 
    let () = unifyGlobal := True in 

    let r1 = entailmentchecking_aux lhs y in 
    
    let r2 = entailmentchecking_helper lhs ys in 
    r1 || r2


let rec entailmentchecking (lhs:normalisedStagedSpec list) (rhs:normalisedStagedSpec list) : (bool) = 
  match (lhs) with 
  | [] -> true 
  | x :: xs -> 
    let r1 = entailmentchecking_helper x rhs in 
    let r2 = entailmentchecking xs rhs in 
    r1 && r2

let normal_report ?(kind="Function") ?given_spec ?given_spec_n ?inferred_spec ?inferred_spec_n ?forward_time_ms ?entail_time_ms ?result name =
  let normed_spec, normed_post =
    let@ _ =
      Debug.span (fun _r -> debug ~at:2 ~title:"final normalization" "")
    in
    let normed_spec =
      match given_spec_n with
      | Some s -> "[Normed   Spec] " ^ string_of_spec_list (normalise_spec_list_aux2 s) ^ "\n\n"
      | None -> ""
    in
    let normed_post =
      match inferred_spec_n with
      | Some s ->
          (*print_endline ("\ninferred_spec_n:");
          let _ = List.iter (fun spec -> print_endline (string_of_normalisedStagedSpec spec) ) s in
          print_endline("\n----------------");

          print_endline (string_of_spec_list (normalise_spec_list_aux2 s)); 
          *)
        "[Normed   Post] " ^ string_of_spec_list (normalise_spec_list (normalise_spec_list_aux2 s)) ^ "\n\n"
      | None -> ""
    in
    normed_spec, normed_post
  in
  debug ~at:2 ~title:"verification result" "";
  let header =
    "\n========== " ^ kind ^ ": "^ name ^" ==========\n" ^
    (match given_spec with
    | Some s -> "[Specification] " ^ string_of_spec_list s ^ "\n\n"
    | None -> "") ^
    normed_spec ^
    (match inferred_spec with
    | Some s -> "[Raw Post Spec] " ^ string_of_spec_list s ^ "\n\n"
    | None -> "") ^
    normed_post ^
    (match forward_time_ms with
    | Some t -> 
      (
      let () = summary_forward := !summary_forward  +. t in   
      "[Forward  Time] " ^ string_of_time t ^ " ms\n")
    | None -> "") ^
    (match result with
    | Some r ->
      let don't_worry = if not r && String.ends_with ~suffix:"_false" name then " (expected)" else "" in 
      "[Entail  Check] " ^ (string_of_res r) ^ don't_worry ^ "\n"
    | None -> "") ^
    (match entail_time_ms with
    | Some t -> 
      (
      let () = summary_entail := !summary_entail  +. t in     
      "[Entail   Time] " ^ string_of_time t ^ " ms\n")
    | None -> "") ^

    (let () = summary_askZ3 := !summary_askZ3  +. !z3_consumption in 
    ("[Z3       Time] " ^ string_of_time !z3_consumption^ " ms\n"))
    
    ^
    (String.init (String.length name + 32) (fun _ -> '=')) ^ "\n"
  in
  Format.printf "%s@." header

let test_report ?kind:_ ?given_spec:_ ?given_spec_n:_ ?inferred_spec:_ ?inferred_spec_n:_ ?forward_time_ms:_ ?entail_time_ms:_ ?result name =
  let false_expected = String.ends_with ~suffix:"_false" name in
  match result with
  | Some true when false_expected ->
    tests_failed := true;
    Format.printf "FAILED: %s@." name
  | Some false when not false_expected ->
    tests_failed := true;
    Format.printf "FAILED: %s@." name
  | _ -> ()

let report_result ?kind ?given_spec ?given_spec_n ?inferred_spec ?inferred_spec_n ?forward_time_ms ?entail_time_ms ?result name =
  let f =
    if !test_mode then test_report else normal_report
  in
  f ?kind ?given_spec ?given_spec_n ?inferred_spec ?inferred_spec_n ?forward_time_ms ?entail_time_ms ?result name


let rec check_remaining_obligations original_fname lems preds obligations =
  let open Search in
  all ~name:"subsumption obligation"
    ~to_s:string_of_pobl
    obligations (fun (params, obl) ->
    let name =
      (* the name of the obligation appears in tests and should be deterministic *)
      let base = "sub_obl" in
      if Str.string_match (Str.regexp ".*_false$") original_fname 0
        then base ^ "_false" else base
    in
    if check_obligation name params lems preds obl
      then succeed
      else fail)

and check_obligation name params lemmas predicates (l, r) =
  let@ _ =
    Debug.span (fun _r ->
        debug ~at:1
          ~title:(Format.asprintf "checking obligation: %s" name) "")
  in
  let open Search in begin
  let res = Entail.check_staged_subsumption_disj name params [] lemmas predicates l r in
  report_result ~kind:"Obligation" ~given_spec:r ~inferred_spec:l ~result:(Search.succeeded res) name;
  let* res = res in
  check_remaining_obligations name lemmas predicates res.subsumption_obl
  end |> Search.succeeded

let check_obligation_ name params lemmas predicates sub =
  check_obligation name params lemmas predicates sub |> ignore

exception Method_failure

let analyze_method prog ({m_spec = given_spec; _} as meth) : core_program =

  let () =  z3_consumption := 0.0 in 
  let time_stamp_beforeForward = Sys.time () in
  let inferred_spec, predicates, fvenv =
    (* the env is looked up from the program every time, as it's updated as we go *)
    let method_env = prog.cp_methods
      (* within a method body, params/locals should shadow functions defined outside *)
      |> List.filter (fun m -> not (List.mem m.m_name meth.m_params))
      (* treat recursive calls as abstract, as recursive functions should be summarized using predicates *)
      |> List.filter (fun m -> not (String.equal m.m_name meth.m_name))
      |> List.map (fun m -> m.m_name, m)
      |> List.to_seq
      |> SMap.of_seq
    in
    let pred_env = prog.cp_predicates in 
    let env = create_fv_env method_env pred_env in
    let inf, env =
      let@ _ =
        Debug.span (fun _ -> debug ~at:2 ~title:"apply forward rules" "")
      in
      infer_of_expression env [freshNormalReturnSpec] meth.m_body
    in

    (* make the new specs inferred for lambdas available to the entailment procedure as predicates *)
    let preds_with_lambdas =
      let lambda =
        env.fv_methods
        |> SMap.filter (fun k _ -> not (SMap.mem k method_env))
        |> SMap.map (fun meth -> Entail.derive_predicate meth.m_name meth.m_params (Option.get meth.m_spec)) (* these have to have specs as they did not occur earlier, indicating they are lambdask *)
        |> SMap.to_seq
      in
      SMap.add_seq lambda prog.cp_predicates
    in
    inf, preds_with_lambdas, env
  in
  (* check misc obligations. don't stop on failure for now *)
  fvenv.fv_lambda_obl |> List.iter (check_obligation_ meth.m_name meth.m_params prog.cp_lemmas predicates);
  fvenv.fv_match_obl |> List.iter (check_obligation_ meth.m_name meth.m_params prog.cp_lemmas predicates);

  (* check the main spec *)
  let time_stamp_afterForward = Sys.time () in

  (*print_endline ("\n----------------\ninferred_spec: \n" ^ string_of_spec_list inferred_spec);*)

  let inferred_spec_n = 
    let@ _ = Debug.span (fun _r -> debug ~at:2 ~title:"normalization" "") in
    try
        
        normalise_disj_spec_aux1 inferred_spec
      with Norm_failure -> report_result ~inferred_spec ~result:false meth.m_name; raise Method_failure
  in




  let res =
    match given_spec with
    | Some given_spec ->
      let given_spec_n =
        let@ _ = Debug.span (fun _r -> debug ~at:2 ~title:"normalization" "") in
        try
          normalise_disj_spec_aux1 given_spec
        with Norm_failure -> report_result ~inferred_spec ~inferred_spec_n ~given_spec ~result:false meth.m_name; raise Method_failure
      in
      let time_stamp_afterNormal = Sys.time () in
      let res =
        try
          let syh_old_entailment = false in
          match syh_old_entailment with
          | true -> entailmentchecking inferred_spec_n given_spec_n
          | false ->
             (*normalization occurs after unfolding in entailment *)

            let inferred_spec, given_spec  =
              let@ _ = Debug.span (fun _r -> debug ~at:2 ~title:"normalization" "") in
              normalise_spec_list inferred_spec, normalise_spec_list given_spec
            in

            (* print_endline ("proving!!!==================================") ;
            print_endline ("inferred_spec " ^ string_of_disj_spec inferred_spec);
            print_endline (" |= ") ;
            print_endline ("given_spec " ^ string_of_disj_spec given_spec); *)
            
            let open Search in begin
              let* res =
                Entail.check_staged_subsumption_disj meth.m_name meth.m_params meth.m_tactics prog.cp_lemmas predicates inferred_spec given_spec
              in 
              check_remaining_obligations meth.m_name prog.cp_lemmas predicates res.subsumption_obl
            end |> succeeded

        with Norm_failure ->
          (* norm failing all the way to the top level may prevent some branches from being explored during proof search. this does not happen in any tests yet, however, so keep error-handling simple. if it ever happens, return an option from norm entry points *)
          false
      in
      let time_stamp_afterEntail = Sys.time () in
      let entail_time_ms = ((time_stamp_afterEntail -. time_stamp_afterNormal) *. 1000.0) in
      let forward_time_ms = ((time_stamp_afterForward -. time_stamp_beforeForward) *. 1000.0) in
      report_result ~inferred_spec ~inferred_spec_n ~given_spec ~given_spec_n ~entail_time_ms ~forward_time_ms ~result:res meth.m_name;
      res
    | None ->
      report_result ~inferred_spec ~inferred_spec_n meth.m_name;
      true
  in
  (* only save these specs for use by later functions if verification succeeds *)
  if not res then prog 
  else (
    let@ _ =
      Debug.span (fun _r ->
          debug ~at:2
            ~title:(Format.asprintf "remembering predicate for %s" meth.m_name) "")
    in
    let prog, pred =
      (* if the user has not provided a predicate for the given function,
        produce one from the inferred spec *)
      let p =
        Entail.derive_predicate meth.m_name meth.m_params inferred_spec
      in
      let cp_predicates = SMap.update meth.m_name
        (function
        | None ->
          Some p
        | Some _ -> None) prog.cp_predicates
      in
      { prog with cp_predicates }, p
    in
    let prog =
      (* if the user has not provided a spec for the given function, remember the inferred method spec for future use *)
      match given_spec with
      | None ->
        (* using the predicate instead of the raw inferred spec makes the induction hypothesis possible with current heuristics. it costs one more unfold but that is taken care of by the current entailment procedure, which repeatedly unfolds *)
        let _mspec : disj_spec = inferred_spec in
        let mspec : disj_spec =
          let prr, ret = unsnoc pred.p_params in
          function_stage_to_disj_spec pred.p_name (List.map (fun v1 -> Var v1) prr) (Var ret)
        in
        (*print_endline ("inferred spec for " ^ meth.m_name ^ " " ^  (string_of_disj_spec mspec)); *)

        debug ~at:1 ~title:(Format.asprintf "inferred spec for %s" meth.m_name) "%s" (string_of_disj_spec mspec);
        let cp_methods = List.map (fun m -> if String.equal m.m_name meth.m_name then { m with m_spec = Some mspec } else m ) prog.cp_methods
        in
        { prog with cp_methods }
      | Some _ -> prog
    in
    prog)

let process_items (strs: structure_item list) : unit =
  strs |>
    List.fold_left (fun (bound_names, prog) c ->
      match Core_lang.transform_str bound_names c with
      | Some (`LogicTypeDecl (name, params, ret, path, lname)) ->
        let def =
          { pft_name = name; pft_params = params; pft_ret_type = ret; pft_logic_name = lname; pft_logic_path = path }
        in
        Globals.global_environment.pure_fn_types <-
          SMap.add name def Globals.global_environment.pure_fn_types;
        bound_names, prog
      | Some (`Lem l) ->
        debug ~at:4 ~title:(Format.asprintf "lemma %s" l.l_name) "%s" (string_of_lemma l);
        let left =
          let (f, ps) = l.l_left in
          let args, ret = unsnoc ps in
          function_stage_to_disj_spec f args ret
        in
        check_obligation_ l.l_name l.l_params prog.cp_lemmas prog.cp_predicates (left, [l.l_right]);
        debug ~at:4 ~title:(Format.asprintf "added lemma %s" l.l_name) "%s" (string_of_lemma l);
        (* add to environment regardless of failure *)
        bound_names, { prog with cp_lemmas = SMap.add l.l_name l prog.cp_lemmas }
      | Some (`Pred p) -> 
        (*print_endline ("\n"^ p.p_name ^  Format.asprintf "(%s)" (String.concat ", " p.p_params) ^ ": ");
        print_endline (string_of_disj_spec p.p_body);
        *)

        let body' = replaceSLPredicatesWithDef p.p_body prog.cp_sl_predicates in 
        (*print_endline ("~~~> " ^ string_of_disj_spec body');
        *)
        let (p': pred_def) = {
          p_name = p.p_name;
          p_params = p.p_params;
          p_body = body';
          p_rec = (find_rec p.p_name)#visit_disj_spec () body';
        } in 
        bound_names, { prog with cp_predicates = SMap.add p'.p_name p' prog.cp_predicates }

      | Some (`SLPred p) -> 
        (*
        print_endline ("\n"^ p.p_sl_name^  Format.asprintf "(%s)" (String.concat ", " p.p_sl_params) ^ ": " ^ Format.asprintf "ex %s; " (String.concat " " p.p_sl_ex) ^ string_of_state p.p_sl_body);
        *)
        bound_names, { prog with cp_sl_predicates = SMap.add p.p_sl_name p prog.cp_sl_predicates }
      | Some (`Eff _) ->
        (* ignore *)
        bound_names, prog
      | Some (`Meth (m_name, m_params, m_spec, m_body, m_tactics, pure_fn_info)) -> 
        (* ASK YAHUI *)
        (* let _m_spec' = 
          (match m_spec with 
          | None -> None 
          | Some spec -> 
          (*print_endline ("\n"^ m_name ^  Format.asprintf "(%s)" (String.concat ", " m_params) ^ ": ");
          print_endline (string_of_disj_spec spec);*)
          let spec' = replacePredicatesWithDef spec prog.cp_methods prog.cp_predicates in 
          (*print_endline ("~~~> " ^ string_of_disj_spec spec');*)
          let spec'' = (replaceSLPredicatesWithDef spec' prog.cp_sl_predicates) in 
          (*print_endline ("~~~> " ^ string_of_disj_spec spec'' ^"\n");*)
          Some spec''
          ) 
        in *)
        (* the right fix is likely to unfold all non-recursive predicates internally before entailment *)
        let m_spec' = m_spec in
        let meth = { m_name=m_name; m_params=m_params; m_spec=m_spec'; m_body=m_body; m_tactics=m_tactics } in

        (* as we handle methods, predicates are inferred and are used in place of absent specifications, so we have to keep updating the program as we go *)
        let prog = { prog with cp_methods = meth :: prog.cp_methods } in

        debug ~at:2 ~title:"parsed" "%s" (string_of_program prog);
        debug ~at:2 ~title:"user-specified predicates" "%s" (string_of_smap string_of_pred prog.cp_predicates);

        let () =
          match pure_fn_info with
          | Some (param_types, ret_type) ->
            let pf =
              { pf_name = m_name; pf_params = List.map2 pair m_params param_types; pf_ret_type = ret_type; pf_body = m_body; }
            in
            Globals.define_pure_fn m_name pf;
          | None -> ()
        in
        begin try
          let prog =
            let@ _ =
              Debug.span (fun _r ->
                  debug ~at:1
                    ~title:(Format.asprintf "verifying function: %s" meth.m_name) "")
            in
            analyze_method prog meth
          in
          m_name :: bound_names, prog
        with Method_failure ->
          (* update program with method regardless of failure *)
          bound_names, prog
        end
      | None -> bound_names, prog
    )
    ([], empty_program)
    |> ignore

let run_string_ line =
  let items = Parser.implementation Lexer.token (Lexing.from_string line) in
  process_items items

let run_string s =
  Provers.handle (fun () -> run_string_ s)

let retriveComments (source:string) : (string list) = 
  let partitions = Str.split (Str.regexp "(\\*@") source in 
  match partitions with 
  | [] -> assert false 
  | _ :: rest -> (*  SYH: Note that specification can't start from line 1 *)
  let partitionEnd = List.map (fun a -> Str.split (Str.regexp "@\\*)")  a) rest in 
  let rec helper (li: string list list): string list = 
    match li with 
    | [] -> []
    | x :: xs  -> 
      (match List.hd x with
      |  head -> 
        if String.compare head "" ==0 then helper xs 
        else 
          let ele = ("/*@" ^ head ^ "@*/") in 
          (ele :: helper xs)  ) 
  in 
  let temp = helper partitionEnd in 
  temp

let run_file inputfile =
(* let outputfile = (Sys.getcwd ()^ "/" ^ Sys.argv.(2)) in
   print_string (inputfile ^ "\n" ^ outputfile^"\n");*)
  let ic = open_in inputfile in
  try
      let lines =  (input_lines ic ) in
      let line = List.fold_right (fun x acc -> acc ^ "\n" ^ x) (List.rev lines) "" in
      
      debug_tokens line;

      run_string line;

      let partitions = retriveComments line in

      let line_of_spec = List.fold_left (fun acc a -> acc + (List.length (Str.split (Str.regexp "\n") a))) 0 partitions in 

      debug ~at:2 ~title:"final summary" "";
      let finalSummary = 
        "\n========== FINAL SUMMARY ==========\n" 
        ^"[  LOC  ] " ^   string_of_int (List.length lines) ^ "\n"
        ^"[  LOS  ] " ^   string_of_int (line_of_spec)  ^ "\n"
        ^"[Forward+Entail] " ^   string_of_float ((!summary_forward +. !summary_entail)/.1000.0)  ^ " s\n"
        ^"[ AskZ3 ] " ^   string_of_float ((!summary_askZ3)/.1000.0)  ^ " s\n"

      
      in 
      if not !test_mode then
        print_endline finalSummary; 


      
      flush stdout;                (* 现在写入默认设备 *)
      close_in ic                  (* 关闭输入通道 *)

    with
    | Pretty.Foo s ->
      print_endline "\nERROR:\n";
      print_endline s
    | e ->                      (* 一些不可预见的异常发生 *)
      close_in_noerr ic;           (* 紧急关闭 *)
      raise e                      (* 以出错的形式退出: 文件已关闭,但通道没有写入东西 *)

   ;;

let main () =
  let inputfile = (Sys.getcwd () ^ "/" ^ Sys.argv.(1)) in
  run_file inputfile;
  if !test_mode && not !tests_failed then Format.printf "ALL OK!@.";
  exit (if !tests_failed then 1 else 0)