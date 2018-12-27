
List.assoc
==========


Ai.add_binding_st
-----------------

+ arrayの対応も必要
+ グローバル変数，array

<details><!--{{{-->

```ocaml
let add_binding_st f rho qs =
  let rho' = add_index rho 0 in
  let qref = try List.assoc rho' (!binding_array_nt).(f) with Not_found -> assert false in
  qref := merge_and_unify compare qs !qref
```


</details><!--}}}-->

Scc.split_list_at
-----------------

+ グローバル変数`visit`のlookup
<details><!--{{{-->

```ocaml
(* グローバル変数 *)
let visited = ref [];;

(* Invariant: [List.mem x l] *)
let rec split_list_at x l =
  match l with
  | [] -> raise Impossible
  | y::l' ->
      if x=y then ([x],l')
      else
        let (l1,l2)=split_list_at x l' in
        (y::l1, l2);;

(* Invariant: [List.mem x !visited] *)
let take_from_visited(x) =
  let (l1,l2) = split_list_at x !visited in
                ^^^^^^^^^^^^^^^^^^^^^^^^
  let _ = visited := l2 in
  l1

let rec visit((g:graph),x,scc) =
  (*** let _ = (print_string "visiting ";print_int x;print_newline()) in***)
  let _ = visit := x::!visit in
  let _ = set_dfsnum g x !dfsnum in
  let _ = set_low g x !dfsnum in
  let _ = inc_dfsnum() in
  let nexts = get_nexts g x in
  let (g',scc') =
    visit_next(g, x, nexts,scc) in
  if get_dfsnum g' x = get_low g' x
  then
    let newscc = take_from_visited(x) in
                 ^^^^^^^^^^^^^^^^^^^^
    let newg = delete_nodes g' newscc in
    (newg, newscc::scc')
  else
    (g',scc')
and visit_next(g, x, nexts,scc) =
  match nexts with
    [] -> (g, scc)
  | y::yl ->
      if List.mem_assoc y g then
        if List.mem y !visited then
          (set_low g x (min (get_low g x) (get_dfsnum g y));
           visit_next(g, x, yl, scc))
        else
          let (g', scc') = visit(g, y, scc) in
          (set_low g x (min (get_low g x) (get_low g y));
           visit_next(g', x, yl, scc'))
      else visit_next(g,x,yl,scc);;
```

+ store-passingすれば行ける？
    + `visit_next`で再帰的に`visit`を呼ぶ部分が厳しい
        + `visit` → `take_from_visited`で`visited`が書き換えられてしまうため`x`が残っている保証が難しい

</details><!--}}}-->

<!--
Grammar.find_dep
----------------

Grammar.find_sc
---------------

`List.find (List.mem _) _`


使われていなかった
-->

Ai.mk_trtab_for_ata
--------------------

+ Invariant:
  + `Conversion.convert_ata`の返り値のオートマトンについて`{a | (f,a) \in \dom(δ)} \subseteq \dom(Σ)`


Cegen.lookup_headty
-------------------

```ocaml
let lookup_headty vte h aty =
  match h with
  | T(a) ->
      let q = Type.codom_of_ity aty in Type.ty_of_t_q a q
  | Var(x) -> (try List.assoc x vte with Not_found -> assert false)
                   ^^^^^^^^^^^^^^^^
  | _ -> assert false (* NT(_) | APP(_,_)*)
```

`vte`はどこから来るか

```
let register_backchain f ity ntyid =
  let (arity,body) = lookup_rule f in
  let vars = mk_vars f arity in
  let (vte,rty) = mk_vte vars ity in
       ^^^
  let eterm = try find_derivation ntyid vte body rty
                  ^^^^^^^^^^^^^^^^^^^^^^^^^
  ...
→ find_derivation ntyid vte term aty (* 再帰 *)
→ find_headtype ntyid vte h aty k
→ lookup_headty vte h aty
```

TODO

Cegen.evaluate_eterm
--------------------

```
let rec evaluate_eterm eterm env =
  let (h,termss) = decompose_eterm eterm in
  match h with
  | ENT(f,ity,ntyid) ->
      begin try
        let (vte,body) =
          try Hashtbl.find tracetab (f,ity) with Not_found ->
            register_backchain f ity ntyid;
            Hashtbl.find tracetab (f,ity)
            ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ Hashtbl.find
        in
        let (vte',body') = rename_vte_eterm vte body in
        let env' = mk_env vte' termss in
                   ^^^^^^
        evaluate_eterm body' (env'@env)
      with Not_found -> assert false end
  | ET(a,_aty) ->
      begin try
        let trees = List.map (fun ts -> evaluate_eterms ts env) termss in
        Node(a, trees)
      with Not_found -> assert false end
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ここは来ないのでは TODO
  | EVar(v,aty) ->
      begin try
        let eterm1 = List.assoc (v,aty) env in
        evaluate_eterm (compose_eterm eterm1 termss) env
      with Not_found -> assert false end
      ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ ここは来ないのでは part2
  | ECoerce(aty1,aty2,t) ->
      begin try
        match (aty1,aty2) with
        | (ItyQ(q1),ItyQ(q2)) -> assert (q1=q2); evaluate_eterm t env
        | (ItyFun(_,ty11,aty11), ItyFun(_,ty21,aty21)) ->
            begin match termss with
            | [] -> assert false
                    ^^^^^^^^^^^^
            | ts::termss' ->
                let tyterms = List.combine ty21 ts in
                let ts' = List.map (fun aty ->
                    let (aty',t') = List.find (fun (aty',_)->Type.subtype aty' aty) tyterms in
                    if aty=aty' then t' else ECoerce(aty',aty,t')) ty11
                in
                let t1 = if aty11=aty21 then EApp(t,ts') else
                    ECoerce(aty11,aty21,EApp(t,ts'))
                in evaluate_eterm (compose_eterm t1 termss') env
            end
        | _ -> assert false
               ^^^^^^^^^^^^
      with Not_found -> assert false end
  | _ -> assert false
and evaluate_eterms ts env =
  match ts with
  | [] -> Bottom
  | t::ts' ->
      let t1 = evaluate_eterm t env in
      let t2 = evaluate_eterms ts' env in
      merge_tree t1 t2
```

TODO
+ 「ここには来ないのでは」は検証できるか


Grammar.arity_of_t
------------------

Σのlookupで難しい

```ocaml
let arity_of_t a = List.assoc a (!gram).t
```

### caller

```ocaml
(* ai.ml *)
let expand_state q a =
  try Hashtbl.find trtab (q,a)
  with Not_found -> Array.make (Grammar.arity_of_t a) []
(* aはprocess_node由来: *)
let process_node (aterm,qs) =
  let (h, termss) = decompose_aterm aterm in
  match h with
  | Ht(a) -> ...
       ^
```

<!--
+ `let terminals = List.map (fun a -> (a, -1)) (terminals_in_rules rules)`でΣは作られる
    + 「rulesに表れるaはterminalsに含まれる」が寺尾さんの手法で示せる？
        + 包含は無理では
+ 「`process_node`に渡される`aterm`は`rules`のsubterm」は示せる？
    + 無理では
-->

```ocaml
(* saturate.ml *)
let mk_linearity_tab() =
  Hashtbl.iter (fun c tyarray ->
      let arity = Grammar.arity_of_t c in
      let a = Array.make arity true in
      Array.iter (fun ty ->
          List.iter (fun ity ->
              register_linearity ity a 0) ty) tyarray;
      Hashtbl.add Ai.tab_linearity c a
    )
    cte
(* Hashtbl *)
```


Saturate.arity_of
-----------------

Σのlookup

```ocaml
let arity_of a m =
  List.assoc a m.alpha

(* caller *)
let automaton2cte m =
  let delta = m.delta in
  init_cte m.alpha m.st;
  let _ = List.iter
      (fun ((q, a), qs) ->
         let ty = tr2ty q qs in
         register_cte_ty (a, ty))
      delta
  in
  let qs = m.st in
  let terminals = List.map fst m.alpha in
  List.iter
    (fun a ->
       let qs1 = (* the set of q s.t. delta(q,a) is undefined *)
         List.filter
           (fun q-> not(List.exists (fun ((q',a'),_)->q=q'&&a=a') delta))
           qs
       in register_cte_ty (a, List.map (fun q->add_topty (arity_of a m) (ItyQ(Ai.state2id q))) qs1))
                                                          ^^^^^^^^
    terminals
```

Saturate.ata2cte
----------------

+ `List.iter`の中でδのlookup

<details><!--{{{-->

```ocaml
let ata2cte m =
  (*  let open AlternatingAutomaton in *)
  init_cte m.AlternatingAutomaton.alpha m.AlternatingAutomaton.st;
  List.iter
    (fun (a,i) ->
      let l = List.concat (List.map (fun q ->
          let fml = List.assoc (q,a) m.AlternatingAutomaton.delta in
                    ^^^^^^^^^^^^^^^^
          let pis = AlternatingAutomaton.prime_implicants fml in
          List.map (build_ity q i) pis) m.AlternatingAutomaton.st) in
      register_cte_ty (a,l))
    m.AlternatingAutomaton.alpha
```

</details><!--}}}-->

Scc.get_node
------------

```ocaml
let get_node (g:graph) x = List.assoc x g
```

`List.find`
===========

Saturate.check_ty_of_term
-------------------------

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

Saturate.pick_vte
-----------------

<details><!--{{{-->

```ocaml
let pick_vte ity ity_vte_list =
  try
    snd(List.find (fun (ity',_vte)-> subtype ity' ity) ity_vte_list )
  with Not_found -> raise Untypable
```

</details><!--}}}-->

Saturate.check_ty_of_term
-------------------------

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

Saturate.ty_of_var
------------------

`List.exist`と同じ

Grammar.find_sc
---------------

`List.find (List.mem _) _`


Saturate.ty_of_var
------------------

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

Cegen.find_derivation
---------------------

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
