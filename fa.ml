
(* ******************************************** *)
(** Basic functions on finite automata *)
(* ******************************************** *)
(**
   Code stub for assignment 1
*)

type symbol = char
type input = char list

type state = string

(* transition function *)
type tf = (state * symbol * state) list

(* initial state * transition function * end state *)
type fa = { states: state list; start:state; tf: tf; final: state list}


(* ******************************************** *)
(* Examples of automata *)
(* ******************************************** *)

let a = {states = ["q0";"q1";"q2"];
         start = "q0";
         tf = [("q0",'a',"q1"); ("q1",'b',"q1"); ("q1",'c',"q2")];
         final = ["q2"]}

let a2 = {states = ["q0";"q1";"q2";"q3";"q4"];
          start = "q0";
          tf = [("q0",'a',"q1"); ("q1",'b',"q1")
               ; ("q1",'c',"q2");  ("q3",'a',"q4")];
          final= ["q2"]
         }
let tf_of_a = [("q0",'a',"q1"); ("q1",'b',"q1"); ("q1",'c',"q2")]



(* ******************************************** *)
(* Helper functions *)
(* ******************************************** *)

let input_of_string s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) []


(* ******************************************** *)
(* Simulating automata *)
(* ******************************************** *)

let rec apply_transition_function tf state symbol : state option = 
  match tf with
  | [] -> None (* There is no state that can be reached with this input on this current state *)
  | (startSt, sym, endSt)(* Each element in the tf list is in this configuration *)::tl when startSt = state && sym = symbol -> Some endSt 
  (* If the input symbol in the current state return works with the current configuration go to the end state in that configuration *)
  | _::tl -> apply_transition_function tl state symbol (* If the state and symbol don't match the current configuration go on to the next one *)



let rec accept_help fa currstate input : bool= 
  match input with (* For each symbol in the input *)
  |[] -> List.mem currstate fa.final (* Input is finished so check if the ending state is an accept state *)
  |h::t -> match apply_transition_function fa.tf currstate h with (* Run the tf function with the current symbol and state *)
    | Some st -> accept_help fa st t (* If the tf function returns some state repeat the process with the next symbol *)
    | None -> false (* Input is invalid *)

let accept fa input : bool = accept_help fa fa.start input



let rec next tf state symbol : state list =
  match tf with
  |[] -> [] (* tf list is done so return the result *)
  |(startSt, sym, endSt)::tl -> if startSt = state && sym = symbol (* If the configutation matches the one that is being looked in the tf *)
    then endSt::next tl state symbol (* Add the end state in that configuration to the list *)
    else next tl state symbol (* Go on to the next configuration in the tf *)

let rec deterministic fa : bool = 
  let rec deterministic_help tf : bool =
    match tf with (* for each configuration in the tf *)
    |(startSt, sym, endSt)::tl -> if List.length (next tf startSt sym) > 1 then false (* There is more than 1 sucessor state with the same state *)
    else deterministic_help tl (* Go on to the next configuration *)
    |[] -> true (* There are no states with more than 1 successor *)
  in deterministic_help fa.tf



let valid fa : bool = List.mem fa.start fa.states (* Start state belongs to the set of states *)
&& List.for_all (fun state -> List.mem state fa.states) fa.final (* All final states belong to the set of states *)
&& deterministic fa (* The fa is deterministic *)


let rec adjacent tf state : state list =
  match tf with
  |[] -> [] (* tf list is done so return the result *)
  |(startSt, sym, endSt)::tl -> if startSt = state (* If the configutation matches the state that is being looked in the tf *)
    then endSt::adjacent tl state (* Add the end state in that configuration to the list *)
    else adjacent tl state (* Go on to the next configuration in the tf *)

let rec modify current visited : state list =
  match current with
  |[] -> []
  |h::tl -> if (List.mem h visited) then modify tl visited else h::modify tl visited 
  (* Remove visited states from the current list to prevent infinite recursion *)

let rec remove_duplicates states: state list =
  match states with
  |[] -> []
  |h::tl -> if (List.mem h tl) then remove_duplicates tl else h::remove_duplicates tl

let rec bfs tf visited current : state list =
  match current with (* For each state that is currently being looked at *)
  |[] -> visited (* There are no more states to look  *)
  |h::tl -> bfs tf (h::visited) (* Add the current state to the visited list *) 
  (tl (* Append the rest of the current states to the new current list *) @ modify (adjacent tf h) visited)
  (* Remove visited states from the list of states adjacent to the current one and become the new current list *)

let reachable fa : state list = remove_duplicates(bfs fa.tf [] [fa.start])


let rec remove_dead_help fa states: state list =
  match states with (* For each state in the list *)
  |[] -> [] (* List is done so return the empty list along with whatever concatenated with it *)
  |h::tl -> if List.mem h (reachable fa) then h::remove_dead_help fa tl (* If state is in reachable state list keep it and move onto next state *)
  else remove_dead_help fa tl (* Current state is not reachable so go onto next state without it *)

let rec remove_dead_help_tf fa tf: (state*symbol*state) list =
  match tf with (* For each tf configuration *)
  |[] -> [] (* All configurations in the tf have been removed so return the new tf list *)
  |(startSt, sym, endSt)::tl -> if List.mem startSt (reachable fa) then (startSt, sym, endSt)::remove_dead_help_tf fa tl (* Keep configuration and go to next *)
  else remove_dead_help_tf fa tl (* The start state in the current configuration was not reachable so disregard it *)

let remove_dead_states fa : fa = 
  match fa with
  |_-> {states = remove_dead_help fa fa.states;
  start = fa.start;
  tf = remove_dead_help_tf fa fa.tf;
  final = remove_dead_help fa fa.final;
  }