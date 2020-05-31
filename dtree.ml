type dTree =
|Leaf of int
|Node of char * dTree * dTree



let tLeft = Node('w',
                    Node('x', 
                            Leaf (2), Leaf (5)),
                    Leaf (8)) 

let tRight = Node('w',
                    Node('x',
                            Leaf (2), Leaf (5)),
                    Node('y',
                            Leaf (7), Leaf (5)))


let rec dTree_height t =  
    match t with  
    |Leaf(x) -> 0  
    |Node(d,lt,rt) -> 1+max (dTree_height lt) (dTree_height rt)

let rec dTree_size t =
    match t with
    |Leaf(x) -> 1
    |Node(d,lt,rt) -> 1 + (dTree_size lt) + (dTree_size rt)

let rec dTree_paths t =
    match t with
    |Leaf(x) -> [[]]
    |Node(d,lt,rt) -> List.map (fun i -> 0::i) (dTree_paths lt) @ List.map (fun i -> 1::i) (dTree_paths rt)

let rec dTree_is_perfect t =
    match t with
    |Leaf(x) -> true
    |Node(d,lt,rt) -> if dTree_height lt = dTree_height rt then dTree_is_perfect lt && dTree_is_perfect rt else false

let rec dTree_map f g t =
    match t with
    |Leaf(x) -> Leaf(g x)
    |Node(d,lt,rt) -> Node(f d, dTree_map f g lt, dTree_map f g rt)



let rec list_to_tree l =
    match l with
    |[] -> Leaf(0)
    |h::tl -> Node(h, list_to_tree tl,list_to_tree tl)


let rec replace_leaf_help t list result =
    match list, t with
    |[], Leaf(_) -> Leaf(result)
    |_, Leaf(_) -> failwith "Error: current path invalid"
    |[], Node(_,_,_) -> failwith "Error: current path invalid"
    |0::tl, Node(d,lt,rt) -> Node(d, replace_leaf_help lt tl result, rt)
    |_::tl, Node(d,lt,rt) -> Node(d, lt, replace_leaf_help rt tl result)
    

let rec replace_leaf_at t f =
    match f with
    |[] -> t
    |(list, result)::tl -> replace_leaf_at (replace_leaf_help t list result) tl

let bf_to_dTree (x,y)=
    replace_leaf_at (list_to_tree x) y

