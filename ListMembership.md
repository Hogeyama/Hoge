
List.assoc
==========


`Ai.add_binding_st`
-------------------

+ arrayの対応も必要

<details><!--{{{-->

```ocaml
let add_binding_st f rho qs =
  let rho' = add_index rho 0 in
  let qref = try List.assoc rho' (!binding_array_nt).(f) with Not_found -> assert false in
  qref := merge_and_unify compare qs !qref
```

</details><!--}}}-->

`Saturate.check_ty_of_term`
---------------------------

<details><!--{{{-->

```ocaml
let rec check_ty_of_term venv term ity =
  match term with
  | App(_,_) ->
      let (h,terms) = Grammar.decompose_term term in
      let tyss = match_head_types h venv (List.length terms) ity in
      let vte = check_argtypes venv terms tyss in vte
  | Var(v) ->
      begin try
        let ity1 = List.find (fun ity1 -> subtype ity1 ity) (ty_of_var venv v) in
                   ^^^^^^^^^
        [(v, [ity1])]
      with
        Not_found -> raise Untypable
      end
  | T(a) ->
      let q = codom_of_ity ity in
      if List.exists (fun ity1 -> subtype ity1 ity) (ty_of_t_q a q)
         ^^^^^^^^^^^
      then []
      else raise Untypable
  | NT(f) ->
      let q = codom_of_ity ity in
      if List.exists (fun ity1 -> subtype ity1 ity) (ty_of_nt_q f q)
         ^^^^^^^^^^^
      then []
      else raise Untypable
```

</details><!--}}}-->

`Scc.split_list_at`
-------------------

`List.mem`に相当

`Grammar.find_dep`
------------------


`Grammar.find_sc`
-----------------

`List.find (List.mem _) _`

`Ai.mk_trtab_for_ata`
---------------------

`let arity = List.assoc a m.AlternatingAutomaton.alpha in`

`Ai.add_binding_st`
-------------------

`let qref = try List.assoc rho' (!binding_array_nt).(f) with Not_found -> assert false in`

`Cegen.lookup_headty`
---------------------

```
match h with
| Var(x) -> (try List.assoc x vte with Not_found -> assert false)
```

`Cegen.evaluate_eterm`
----------------------

```
| EVar(v,aty) ->
    begin try
      let eterm1 = List.assoc (v,aty) env in
      evaluate_eterm (compose_eterm eterm1 termss) env
     with Not_found -> assert false end
```

`Grammar.find_dep`
------------------

```
let find_dep x dmap =
  try
    List.assoc x dmap
  with Not_found ->
    assert false (* raise (UndefinedNonterminal (name_of_nt x)) *)
```

`Grammar.arity_of_t`
--------------------

```ocaml
let arity_of_t a = List.assoc a (!gram).t
```

`Saturate.arity_of`
-------------------

```
let arity_of a m =
  List.assoc a m.alpha
```

`Saturate.ata2cte`
------------------

+ `List.iter`の中

<details><!--{{{-->

```ocaml
let ata2cte m =
  (*  let open AlternatingAutomaton in *)
  init_cte m.AlternatingAutomaton.alpha m.AlternatingAutomaton.st;
  List.iter
    (fun (a,i) ->
      let l = List.concat (List.map (fun q ->
          let fml = List.assoc (q,a) m.AlternatingAutomaton.delta in
          let pis = AlternatingAutomaton.prime_implicants fml in
          List.map (build_ity q i) pis) m.AlternatingAutomaton.st) in
      register_cte_ty (a,l))
    m.AlternatingAutomaton.alpha
```

</details><!--}}}-->

`Scc.get_node`
--------------

```ocaml
let get_node (g:graph) x = List.assoc x g;;
```



`List.find`
===========

`Saturate.pick_vte`
-------------------

<details><!--{{{-->

```ocaml
let pick_vte ity ity_vte_list =
  try
    snd(List.find (fun (ity',_vte)-> subtype ity' ity) ity_vte_list )
  with Not_found -> raise Untypable
```

</details><!--}}}-->

`Saturate.check_ty_of_term`
---------------------------

<details><!--{{{-->

```ocaml
let rec check_ty_of_term venv term ity =
  match term with
  | App(_,_) ->
      let (h,terms) = Grammar.decompose_term term in
      let tyss = match_head_types h venv (List.length terms) ity in
      let vte = check_argtypes venv terms tyss in vte
  | Var(v) ->
      begin try
        let ity1 = List.find (fun ity1 -> subtype ity1 ity) (ty_of_var venv v) in
                   ^^^^^^^^^
        [(v, [ity1])]
      with
        Not_found -> raise Untypable
      end
  | T(a) ->
      let q = codom_of_ity ity in
      if List.exists (fun ity1 -> subtype ity1 ity) (ty_of_t_q a q)
         ^^^^^^^^^^^
      then []
      else raise Untypable
  | NT(f) ->
      let q = codom_of_ity ity in
      if List.exists (fun ity1 -> subtype ity1 ity) (ty_of_nt_q f q)
         ^^^^^^^^^^^
      then []
      else raise Untypable
```

</details><!--}}}-->

`Saturate.ty_of_var`
--------------------

`List.exist`と同じ

`Grammar.find_sc`
-----------------

`List.find (List.mem _) _`


`Saturate.ty_of_var`
--------------------

+ 別の引数`i`に依存する

````ocaml
let rec ty_of_var venv (f,i) =
  match venv with
  | [] -> assert false
  | (j1,j2,tys)::venv' ->
      if j1<=i && i<=j2 then
        proj_tys f (i-j1) tys
      else ty_of_var venv' (f,i)
````

`Cegen.find_derivation`
------------------------

<details><!--{{{-->
```ocaml
let rec find_derivation ntyid vte term aty =
  let (h,terms) = Grammar.decompose_term term in
  let k = List.length terms in
  let head_typings = find_headtype ntyid vte h aty k in
  try
    List.iter (fun (eh,aty0) ->
        try
          let (eterms,rty) = find_derivation_terms ntyid vte terms aty0 in
          let eterm1 = compose_eterm eh eterms in
          let eterm2 =
            if rty=aty then eterm1
            else ECoerce(rty,aty,eterm1)
          in raise (Found eterm2)
        with Not_found -> ()
      ) head_typings; raise Not_found
                      ^^^^^^^^^^^^^^^
  with Found eterm -> eterm

let register_backchain f ity ntyid =
  let (arity,body) = lookup_rule f in
  let vars = mk_vars f arity in
  let (vte,rty) = mk_vte vars ity in
  let eterm = try find_derivation ntyid vte body rty
    with Not_found ->
      (print_string ("failed to find a derivation for "^(name_of_nt f)^":");
       Type.print_ity ity; assert false)
                           ^^^^^^^^^^^^
  in
  Hashtbl.add tracetab (f,ity) (vte,eterm)
```
</details><!--}}}-->


---

<!--

stype.ml|149 col 29| let lookup_stype_t a cste = List.assoc a cste
  されない @tcheck_term

以下catchされる関数

Saturate.check_ty_of_term
saturate.ml|901 col 10| else raise Untypable
  List.exists
saturate.ml|901 col 10| else raise Untypable
  List.find
saturate.ml|901 col 10| else raise Untypable
  List.exists
saturate.ml|906 col 10| else raise Untypable
  List.exists
saturate.ml|911 col 11| [] -> raise Untypable
  merge_two_vtes vte0 (check_argtypes_aux venv terms tys)でUntypableを投げないものが存在する
  Untypableはcatchされる (`update_ty_of_nt_inc_for_nt_sub_venv`)
alternatingAutomaton.ml|18 col 15| let cls = List.assoc v delta in
alternatingAutomaton.ml|30 col 15| let fml = List.assoc v delta in
automaton.ml|14 col 3| List.assoc (q,a) m.delta
  使われない
cegen.ml|237 col 30| | EVar(v,ity) -> (try EVar(List.assoc v vmap, ity) with Not_found -> eterm)
conversion.ml|49 col 36| Syntax.Name(s) -> (try Var(List.assoc s vmap) with Not_found -> T(s))
grammar.ml|162 col 9| List.assoc x s
grammar.ml|171 col 9| List.assoc x s
scc.ml|52 col 31| let (_,_,nextr) = List.assoc x g in
scc.ml|57 col 20| try (let _ = List.assoc y g' in g') with
scc.ml|154 col 29| let (nextr,_) = List.assoc x g in
scc.ml|159 col 20| try (let _ = List.assoc y g' in g') with
scc.ml|163 col 25| let (nextr, cacher) = List.assoc n g in
  使われない関数
stype.ml|55 col 21| STvar v -> (try List.assoc v sub with Not_found -> st)
utilities.ml|235 col 5| List.assoc var s
utilities.ml|321 col 9| (* like List.assoc, but with a specialized equality function *)

-->
