
<a name = "take_from_visited"></a>
### Scc.take_from_visited

```ocaml
type take_from_visited
  :  { x : int | List.mem x !visited }
  -> int list
let take_from_visited x =
   let (l1,l2) = split_list_at x !visited in
   let _ = visited := l2 in
     l1;;

type split_list_at
  :  (x : int)
  -> { l : int list | List.mem x l }
  -> int list * int list
let rec split_list_at x l =
  match l with
    [] -> raise Impossible
  | y::l' ->
        if x=y then ([x],l')
        else
          let (l1,l2)=split_list_at x l' in
             (y::l1, l2);;
```

