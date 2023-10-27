open Hipcore.Debug

let ( let* ) = Option.bind
let ( let+ ) a f = Option.map f a
let succeeded = Option.is_some
let ok = Some ()
let fail = None
let check b = if b then ok else fail
let or_else o k = match o with None -> k () | Some _ -> o
let pure a = Some a

let all_ : to_s:('a -> string) -> 'a list -> ('a -> 'b option) -> 'b list option
    =
 fun ~to_s vs f ->
  let rec loop rs vs =
    match vs with
    | [] -> Some []
    | x :: xs ->
      info ~title:"(all)" "%s" (to_s x);
      let res = f x in
      (match res with None -> None | Some r -> loop (r :: rs) xs)
  in
  match vs with
  (* special case *)
  | [x] -> f x |> Option.map (fun y -> [y])
  | _ -> loop [] vs

let all : to_s:('a -> string) -> 'a list -> ('a -> 'b option) -> unit option =
 fun ~to_s vs f -> all_ ~to_s vs f |> Option.map (fun _ -> ())

let any :
    name:string ->
    to_s:('a -> string) ->
    'a list ->
    ('a -> 'b option) ->
    'b option =
 fun ~name ~to_s vs f ->
  match vs with
  | [] ->
    (* Error (rule ~name "choice empty") *)
    failwith (Format.asprintf "choice empty: %s" name)
    (* special case *)
  | [x] -> f x
  | v :: vs ->
    let rec loop v vs =
      info ~title:"(any)" "%s" (to_s v);
      let res = f v in
      match (res, vs) with
      | Some r, _ -> Some r
      | None, [] -> None
      | None, v1 :: vs1 -> loop v1 vs1
    in
    loop v vs

let ensure cond = if cond then ok else fail

let either :
    name:string ->
    (* to_s:(bool -> string) -> *)
    (bool -> 'b option) ->
    'b option =
 fun ~name f -> any ~name ~to_s:string_of_bool [true; false] f