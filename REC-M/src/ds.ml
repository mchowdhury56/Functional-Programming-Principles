
(* This file defines expressed values and environments *)


(* expressed values and environments are defined mutually recursively *)

type exp_val =
  | NumVal of int
  | BoolVal of bool
  | UnitVal
  | PairVal of exp_val*exp_val
  | ProcVal of string*Ast.expr*env
  | RecordVal of (string*exp_val) list
  | ListVal of exp_val list
and
  env =
  | EmptyEnv
  | ExtendEnv of string*exp_val*env
  | ExtendEnvRec of Ast.decs*env

(* Expressed Result *)
                 
type 'a result = Ok of 'a | Error of string

type 'a ea_result = env -> 'a result
  
let return (v:'a) : 'a ea_result =
  fun _env ->
  Ok v

let error (s:string) : 'a ea_result =
  fun _env ->
  Error s

let (>>=) (c:'a ea_result) (f: 'a -> 'b ea_result) : 'b ea_result =
  fun env ->
  match c env with
  | Error err -> Error err
  | Ok v -> f v env

let (>>+) (c:env ea_result) (d:'a ea_result): 'a ea_result =
  fun env ->
  match c env with
  | Error err -> Error err
  | Ok newenv -> d newenv


let run (c:'a ea_result) : 'a result =
  c EmptyEnv

let sequence (cs: ('a ea_result) list) : ('a list) ea_result  =
  let mcons p q = p >>= fun x -> q >>= fun y -> return (x::y)
  in List.fold_right mcons cs (return []) 

let mapM (f:'a -> 'b ea_result) (vs:'a list) : ('b list) ea_result = sequence (List.map f vs)


(* Operations on environments *)
let empty_env : unit -> env ea_result =
  fun () ->
    return EmptyEnv

let extend_env : string -> exp_val -> env ea_result =
  fun id v env ->
    Ok (ExtendEnv(id,v,env))


let extend_env_rec : Ast.decs -> env ea_result = fun decs env  ->
  Ok (ExtendEnvRec(decs,env))

let rec list_of_recs : string -> Ast.decs -> env -> exp_val = fun id decs env  ->
  match decs with
  | (v, par, body)::tl ->  if v = id
    then ProcVal(par,body,env)
    else list_of_recs id tl env
  | [] -> ListVal []

let rec apply_env : string -> exp_val ea_result =
  fun id env -> 
  match env with
  | EmptyEnv -> Error (id^" not found!")
  | ExtendEnv(v,ev,tail) ->
    if id=v
    then Ok ev
    else apply_env id tail
  | ExtendEnvRec(decs,tail) ->
    (match (list_of_recs id decs env) with
    | ProcVal(par,body,_) -> Ok( ProcVal(par, body, env) )
    | _ -> apply_env id tail)
      
let lookup_env : env ea_result =
  fun env ->
  Ok env

(* operations on expressed values *)

let int_of_numVal : exp_val -> int ea_result =  function
  |  NumVal n -> return n
  | _ -> error "Expected a number!"

let bool_of_boolVal : exp_val -> bool ea_result =  function
  |  BoolVal b -> return b
  | _ -> error "Expected a boolean!"

let pair_of_pairVal : exp_val -> (exp_val*exp_val) ea_result = function
  | PairVal(v1,v2) -> return (v1,v2)
  | _ -> error "Expected a pair!"

let fields_of_recordVal : exp_val -> ((string*exp_val) list) ea_result = function
  | RecordVal(fs) -> return fs
  | _ -> error "Expected a record!"

let list_of_listVal : exp_val -> (exp_val list) ea_result = function
  | ListVal(vs) -> return (vs)
  | _ -> error "Expected a list!"

let rec string_of_list_of_strings = function
  | [] -> ""
  | [id] -> id
  | id::ids -> id ^ "," ^ string_of_list_of_strings ids


let rec string_of_expval = function
  |  NumVal n -> "NumVal " ^ string_of_int n
  | BoolVal b -> "BoolVal " ^ string_of_bool b
  | UnitVal -> "UnitVal "
  | ProcVal (id,body,env) -> "ProcVal ("^ id ^","^Ast.string_of_expr
                               body^","^ string_of_env' env^")"
  | PairVal(v1,v2) -> "PairVal("^string_of_expval
                        v1^","^string_of_expval v2^")"
  | RecordVal(fs) -> "RecordVal("^List.fold_left (fun s (id,ev) ->
      s ^","^id ^"="^string_of_expval
                        ev) "" fs ^")"
     | _ -> failwith "string_of_expval: ListVal case not implemented" 
and
  string_of_env'  = function
  | EmptyEnv -> "[]"
  | env -> "["^string_of_env'' env^"]"
and
  string_of_env''= function
  | EmptyEnv -> "\n"
  | ExtendEnv(id,v,env) -> string_of_env'' env^" ("^id^":="^string_of_expval v^")\n"
  | ExtendEnvRec(decs,env) -> string_of_env'' env^"
  ("^Ast.string_of_decs decs^")\n"
  


let string_of_env : string ea_result =
  fun env ->
  Ok ("Environment:\n"^ string_of_env' env)

