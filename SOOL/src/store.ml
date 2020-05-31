type 'a t = { mutable data: 'a array; mutable size: int}
  (* data is declared mutable so the store may be resized *)

let empty_store : int -> 'a -> 'a t =
  fun i v -> { data=Array.make i v; size=0 }

let get_size : 'a t -> int =
  fun st -> st.size

let enlarge_store : 'a t -> 'a -> unit =
  fun st v ->
  let new_array = Array.make (st.size*2) v
  in Array.blit st.data 0 new_array 0 st.size;
  st.data<-new_array
    
let new_ref : 'a t -> 'a -> int =
  fun st v ->
  if Array.length (st.data)=st.size      
  then enlarge_store st v
  else ();
  begin
    st.data.(st.size)<-v;
    st.size<-st.size+1;
    st.size-1
  end


let deref : 'a t -> int -> 'a option =
  fun st l ->
  if l>=st.size
  then None (* Index out of bounds *)
  else Some (st.data.(l))

let set_ref :  'a t -> int -> 'a -> unit option =
  fun st l v ->
  if l>=st.size
  then None (* Index out of bounds *)
  else Some (st.data.(l)<-v)
           

let rec take n = function
  | [] -> []
  | x::xs when n>0 -> x::take (n-1) xs
  | _ -> []
             
let string_of_store' f st =
  let ss = List.mapi (fun i x -> (i,f x)) @@ take st.size @@ Array.to_list st.data
  in 
  if ss==[]
  then "Empty"
  else List.fold_left (fun curr (i,s) -> curr^string_of_int i^"->"^s^"\n")
        ""
        ss 

let string_of_store f st =
  "Store:\n"^ string_of_store' f st
