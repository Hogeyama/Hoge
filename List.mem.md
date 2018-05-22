
### Scc.split_list_at
<a name = "split_list_at"></a>

再帰を使う

```ocaml scc.ml
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

### Cegen.lookup_headty
<a name = "lookup_headty"></a>

ADTのパターンマッチとの組み合わせ．

```ocaml cegen.ml
type lookup_headty
  :  (vte : (Grammar.nameV * Grammar.ty) list)
  -> { h : Grammar.term
     | is_T h && Hashtbl.mem a Type.cte ||
       is_Var h && List.mem_assoc (un_Var h) vte
     }
  -> Grammar.ty
let lookup_headty vte h aty =
  match h with
    T(a) ->
      let q = Type.codom_of_ity aty in
        Type.ty_of_t_q a q
  | Var(x) -> (try List.assoc x vte with Not_found -> assert false)
  | _ -> assert false
(* `Type.ty_of_t_q`もfailし得る *)
external type Type.ty_of_t_q
  :  (a : Grammar.nameT)
  -> Grammar.ity list
```

### Ai.add_binding_st
<a name = "add_binding_st"></a>

TODO

```ocaml ai.ml
let add_binding_st f rho qs =
  let rho' = add_index rho 0 in
  let qref = try List.assoc rho' (!binding_array_nt).(f)
             with Not_found -> assert false in
    qref := merge_and_unify compare qs !qref
```

ここから変種

### Grammar.find_sc
<a name = "find_sc"></a>

```ocaml grammar.ml
type find_sc
  :  (f : int)
  -> {scc : int list list | List.mem f (List.concat scc) }
  -> int list
let find_sc f scc =
  let scc' = List.filter (fun x-> List.mem f x) scc in
    match scc' with
      [] -> assert false
    | sc::_ -> sc
```

### Saturate.ty_of_var
<a name = "add_binding_st"></a>

```ocaml saturate.ml
type ty_of_var
  :  (venv : (int * int * 'a array) list)
  -> { ((f, i) : (int * int))
     | List.exist (fun (j1,j2,_) -> j1 <= i && i <= j2) venv
     }
  -> 'a
let rec ty_of_var venv (f,i) =
  match venv with
    [] -> assert false
  | (j1,j2,tys)::venv' ->
    if j1<=i && i<=j2 then
       proj_tys f (i-j1) tys
    else ty_of_var venv' (f,i)
```





