

### Utilityies.list_take_n
<a name = "list_take_n"></a>

```ocaml utilities.ml
type list_take_n
  :  (l: int list)
  -> {m: int | 0 <= m && m < List.length l}
  -> int |len: len = m| list
let rec list_take_n l n =
  if n=0 then []
  else
    match l with
      [] -> assert false
    | x::l' -> x::(list_take_n l' (n-1))
```


