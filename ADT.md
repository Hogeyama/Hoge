
ADT固有のsize function
======================

Cegen.mk_vte
------------

arity

<details><!--{{{-->

```ocaml
type ity = ItyQ of ity_id | ItyFun of ity_id * ty * ity
let rec arity = function
  | ItyQ(_) -> 0
  | ItyFun(_,_,ity) -> 1 + arity ity

(*{SPEC}
type mk_vte : (vars : int list) -> { at : ity | arity at >= List.length vars } -> ...
{SPEC}*)
let rec mk_vte vars at =
  match at with
  | ItyQ(q) ->
      if vars=[] then
        ([], ItyQ(q))
      else assert false
  | ItyFun(_, ty, aty1) ->
      begin match vars with
      | [] -> ([], at)
      | v::vars' ->
          let (ve1, rt1) = mk_vte vars' aty1 in
        ((v, ty)::ve1, rt1)
      end
```

### caller

```ocaml
let register_backchain f ity ntyid =
  let (arity,body) = lookup_rule f in
  let vars = mk_vars f arity in
  let (vte,rty) = mk_vte vars ity in
  let eterm = try find_derivation ntyid vte body rty
    with Not_found ->
      (print_string ("failed to find a derivation for "^(name_of_nt f)^":");
       Type.print_ity ity; assert false)
  in
  Hashtbl.add tracetab (f,ity) (vte,eterm)
```

`let (arity,body) = lookup_rule f`のとき`body`のarityが`arity`以上であることを言うのが難しそう（グローバル変数への書き込み）
関連する関数:

```ocaml
(* grammer.ml *)
let get_def (f: nameNT) (g:gram) =
  g.r.(f)
let lookup_rule (f: nameNT) =
  get_def f (!gram)

(* conversion.ml *)
let Conversion.prerules2gram prerules =
  let prerules = elim_fun_from_prerules prerules in
  let ntnames = List.map (fun (x,_,_)->x) prerules in
  let num_of_nts = List.length ntnames in
  let _ = (ntauxid := num_of_nts) in
  let _ = nttab := Array.make num_of_nts (dummy_ntname,O) in
  let _ = List.iter register_nt ntnames in
  let rules = Array.make num_of_nts (0,dummy_term) in
  let vinfo = Array.make  num_of_nts [| |] in
  let _ = prerules2rules rules vinfo prerules in
  let (nt', rules') =
    if !(Flags.normalize) then
      add_auxiliary_rules !nttab rules
    else (!nttab, rules)
  in
  let s = 0 in
  let terminals = List.map (fun a -> (a, -1)) (terminals_in_rules rules) in
  let g = {nt= nt'; t=terminals; vinfo = vinfo; r=rules'; s=s} in
  Grammar.gram := g; g
  ^^^^^^^^^^^^^^^^^
```

</details><!--}}}-->

<a name = "Saturate__split_ity"></a>
Saturate.split_ity
------------------

arity

```ocaml
let rec split_ity arity ity =
  if arity=0 then ([],ity)
  else match ity with
    | ItyFun(_,ty,ity1)->
        let (tys,ity') = split_ity (arity-1) ity1 in
        (ty::tys, ity')
    | _ -> assert false

(* caller *)
let ty_of_term2 venv term =
  let (h,terms) = Grammar.decompose_term term in
  let ty = ty_of_head h venv in
  let arity = List.length terms in
  let tys_ity_list = List.map (split_ity arity) ty in
  check_args tys_ity_list terms venv []
```

+ `let (h, ts) = decompose_term t`として`h`につく各型`ty`について `length ts <= tyのarity`
+ `ty_of_head`がグローバル変数を使っているので厳しいか


Saturate.get_range
------------------

`Saturate.split_ity`と大体同じ

```ocaml
(* `ity`のarityが`arity`以上 *)
let rec get_range ity arity =
  if arity=0 then ity
  else
    match ity with
    | ItyFun(_,_,ity1) -> get_range ity1 (arity-1)
    | _ -> assert false
```

### caller

```
let match_head_ity h venv arity ity =
  match ity with
  | ItyQ(q) ->
      (match h with
         Var(v) ->
           if !num_of_states=1 then
             let ty = (ty_of_var venv v) in
             List.map (fun ity1 -> get_argtys arity ity1) ty
           else
             let ty = List.filter (fun ity1->codom_of_ity ity1=q) (ty_of_var venv v) in
             List.map (fun ity1 -> get_argtys arity ity1) ty
       | _ ->
           let ty = ty_of_head_q2 h venv q in
           List.map (fun ity1 -> get_argtys arity ity1) ty
      )
  | _ ->
      let q = codom_of_ity ity in
      let ty = List.filter
          (fun ity1 -> subtype (get_range ity1 arity) ity)
                                ^^^^^^^^^
          (ty_of_head_q2 h venv q) in
      List.map (fun ity -> get_argtys arity ity) ty

let ty_of_head_q2 h venv q =
  match h with
  | NT(f) -> ty_of_nt_q f q
             ^^^^^^^^^^
  | T(a) -> ty_of_t_q a q
  | Var(v) -> ty_of_var venv v
  | _ -> assert false
```

`ty_of_nt_q`などがグローバル変数を使っているのでこれも厳しい

+ その他のcaller
    + `match_head_types`: ほぼ同じ


Saturate.get_argtys
-------------------

arity

```ocaml
(* `ity`のarityが`arity`以上 *)
let rec get_argtys arity ity =
  if arity=0 then []
  else
    match ity with
    | ItyFun(_,ty,ity1) -> ty::(get_argtys (arity-1) ity1)
    | _ -> assert false
```

### caller

<details><!--{{{-->

```ocaml
let match_head_ity h venv arity ity =
  match ity with
  | ItyQ(q) ->
      (match h with
         Var(v) ->
           if !num_of_states=1 then
             let ty = ty_of_var venv v in
             List.map (fun ity1 -> get_argtys arity ity1) ty
                                   ^^^^^^^^^^
           else
             let ty = List.filter (fun ity1->codom_of_ity ity1=q) (ty_of_var venv v) in
             List.map (fun ity1 -> get_argtys arity ity1) ty
                                   ^^^^^^^^^^
       | _ ->
           let ty = ty_of_head_q2 h venv q in
           List.map (fun ity1 -> get_argtys arity ity1) ty
                                 ^^^^^^^^^^
      )
  | _ -> (* ItyFun *)
      let q = codom_of_ity ity in
      let ty = List.filter
          (fun ity1 -> subtype (get_range ity1 arity) ity)
          (ty_of_head_q2 h venv q) in
      List.map (fun ity -> get_argtys arity ity) ty
                           ^^^^^^^^^^
```

```ocaml
let match_head_types h venv arity ity =
  match ity with
  | ItyQ(q) ->
      begin match h with
      | Var(v) ->
          let ty = ty_of_var venv v in
          let ty' =
            if !num_of_states=1
            then ty
            else List.filter (fun ity1->codom_of_ity ity1=q) ty
          in
          List.map (fun ity1 -> (get_argtys arity ity1, [(v,[ity1])])) ty'
                                 ^^^^^^^^^^
      | _ ->
          let ty = ty_of_head_q2 h venv q in
          List.map (fun ity1 -> (get_argtys arity ity1, [])) ty
                                 ^^^^^^^^^^
      end
  | _ ->
      let ty = List.filter (fun (ity1,_) ->
          subtype (get_range ity1 arity) ity) (ty_of_head_q h venv (codom_of_ity ity)) in
      List.map (fun (ity,vte) -> (get_argtys arity ity, vte)) ty
                                  ^^^^^^^^^^
```

```ocaml
let rec check_ty_of_term_inc venv term ity f tyf =
  let (h,terms) = Grammar.decompose_term term in
  let arity = List.length terms in
  let tyss =
    if h=NT(f) then
      let ty1 = List.filter (fun ity1 -> subtype (get_range ity1 arity) ity) tyf in
      if ty1=[]
      then raise Untypable
      else List.map (fun ity -> (get_argtys arity ity, [])) ty1
                                 ^^^^^^^^^^
    else
      match_head_types h venv arity ity
  in
  let vte = check_argtypes_inc venv terms tyss f tyf in vte
```

```ocaml
let rec tcheck_wo_venv_inc term ity g ty_g =
  match term with
    Var(x) -> [[(x,[ity])]]
  | T(a) ->
      let q = codom_of_ity ity in
      let ty = (ty_of_t_q a q) in
      if List.exists (fun ity1->subtype ity1 ity) ty then
        [[]]
      else []
  | NT(f)->
      let ty = if f=g then ty_g else
          let q = codom_of_ity ity in ty_of_nt_q f q
      in
      if List.exists (fun ity1->subtype ity1 ity) ty then
        [[]]
      else []
  | App(_,_) ->
      let (h,terms)=Grammar.decompose_term term in
      let arity = List.length terms in
      let tyss =
        if h=NT(g) then
          let ty = List.filter (fun ity1 ->
              subtype (get_range ity1 arity) ity) ty_g in
          List.map (fun ity -> get_argtys arity ity) ty
                               ^^^^^^^^^^
        else match_head_ity h [] arity ity
      in
      List.fold_left
        (fun vtes tys ->
           (tcheck_terms_wo_venv_inc terms tys g ty_g)@vtes) [] tyss
```
</details><!--}}}-->

<a name = "Pobdd__make_node"></a>
Pobdd.make_node
---------------

再帰的ではないが同じ扱いができそうなためこの分類

+ `assert (node_id t1 <> node_id t2)`
+ caller
    + `bdd_var`, `bdd_nvar`, `neg`, `bdd_and`, `bdd_or`, `exists_vl`, `forall_vl`, `imp_and_exists`, `restrict_sorted`
    + `neg`以外は呼び出し前にcheckが入る (`if node_id t1 = node_id t2 then ... else make_node t1 t2`)
        + [ここ](./TrivialProblem.md#Pobdd__make_node)
+ `neg`が問題

<details><!--{{{-->

```ocaml
let node_id = function
  | Leaf(true) -> 0
  | Leaf(false) -> 1
  | Node(_,_,_,x,_) -> x;;
let make_node (v,t1,t2) =
  let i1 = node_id t1 in
  let i2 = node_id t2 in
  assert (i1 <> i2);
  ^^^^^^^^^^^^^^^^^^
  ...

let neg t1 =
  let memo = ref Op1Map.empty in
  let rec go = function
    | Leaf b -> Leaf (not b)
    | Node (v, t1, t2, id,_) ->
      if Op1Map.mem id !memo then Op1Map.find id !memo
      else begin
        let t1' = go t1 in
        let t2' = go t2 in
        let t = make_node (v,t1',t2') in
                ^^^^^^^^^
        memo := Op1Map.add id t !memo;
        t
      end
  in go t1;;
```

</details><!--}}}-->


その他複雑なもの
================

Saturate.check_args
-------------------

  + リストの長さが同じリスト

    <details><!--{{{-->

    ```ocaml
    (* tysとtermsの長さが等しい *)
    let rec check_args_aux tys terms venv =
      match (tys,terms) with
      | ([], []) -> true
      | (ty::tys', t::terms') ->
          List.for_all (fun ity-> check_term t ity venv) ty
            && check_args_aux tys' terms' venv
      | _ -> assert false
             ^^^^^^^^^^^^ tysとtermsの長さが同じ
    (* tys_ity_list の各要素 (tys,ity)に対してtysとtermsの長さが等しい *)
    and check_args tys_ity_list terms venv ty =
      match tys_ity_list with
      | [] -> ty
      | (tys,ity)::tys_ity_list' ->
          if check_args_aux tys terms venv
             ^^^^^^^^^^^^^^
          then
            (if !Flags.merge_vte then
               let ty' = List.filter (fun ity1->not(eq_ity ity ity1)) ty in
               let tys_ity_list'' =
                 List.filter (fun (_,ity1)->not(eq_ity ity ity1)) tys_ity_list'
               in
               check_args tys_ity_list'' terms venv (ity::ty')
             else
               let ty' = List.filter (fun ity1->not(subtype ity ity1)) ty in
               let tys_ity_list'' =
                 List.filter (fun (_,ity1)->not(subtype ity ity1)) tys_ity_list'
               in
               check_args tys_ity_list'' terms venv (ity::ty')
            )
          else
            check_args tys_ity_list' terms venv ty
    and check_term term ity venv =
      match term with
      | App(_,_) ->
          let (h,terms) = Grammar.decompose_term term in
          let tyss = match_head_ity h venv (List.length terms) ity in
          List.exists (fun tys->check_args_aux tys terms venv) tyss
                                ^^^^^^^^^^^^^^
      | Var(v) -> List.exists (fun ity1 -> subtype ity1 ity) (ty_of_var venv v)
      | T(a) -> let q = codom_of_ity ity in
          List.exists (fun ity1 -> subtype ity1 ity) (ty_of_t_q a q)
      | NT(f) -> let q = codom_of_ity ity in
          List.exists (fun ity1 -> subtype ity1 ity) (ty_of_nt_q f q)

    (* caller *)
    let ty_of_term2 venv term =
      let (h,terms) = Grammar.decompose_term term in
      let ty = ty_of_head h venv in
      let arity = List.length terms in
          ^^^^^^^^^^^^^^^^^^^^^^^^^
      let tys_ity_list = List.map (split_ity arity) ty in
      check_args tys_ity_list terms venv []
    ```

    [`split_ity`](./#Saturate__split_ity)は引数と同じ長さのリストを返す

    </details><!--}}}-->

  + 似ている関数（callerは追えていない）
      + `Saturate.check_argtypes_aux`

      + `Saturate.check_argtypes_inc_aux`

      + `Saturate.tcheck_terms_w_venv`

      + `Saturate.tcheck_terms_wo_venv`

      + `Saturate.tcheck_terms_wo_venv_inc`


Cegen.merge_tree
----------------

+ 木がmergeできる
    + Bottomと任意の木はmergeできる
    + Nodeどうしは次の条件を満たすときmergeできる
        + ラベルが等しく
        + 子の数が等しく
        + 対応する子がmergeできる

<details>

```ocaml
let rec merge_tree t1 t2 =
  match t1, t2 with
  | Bottom, _ -> t2
  | _, Bottom -> t1
  | Node(a1,ts1), Node(a2,ts2) ->
      if a1=a2 then
        Node(a1, merge_trees ts1 ts2)
      else assert false
and merge_trees ts1 ts2 =
  List.map (fun (t1,t2) -> merge_tree t1 t2) (List.combine ts1 ts2)
i                                              ^^^^^^^^^^^^
```

</details>

Cegen.mk_env
------------

  + リストの長さについて複雑な条件
  + callerもHashtblが絡んでくるので難しい

<details><!--{{{-->

```ocaml
let rec mk_env vte termss =
  match (vte, termss) with
  | ([], []) -> []
  | ((v,ty)::vte', ts::termss') ->
      let x = List.combine ty ts in
              ^^^^^^^^^^^^
      (List.map (fun (ity,t)->((v,ity),t)) x)@(mk_env vte' termss')
  | _ -> assert false
(* 下とほぼ同じ
let rec mk_env vte termss =
  List.concat @@ List.map2
    begin fun (v,ty) (ts) ->
      let x = List.combine ty ts in
      List.map (fun (ity,t)->((v,ity),t)) x
    end
    vte termss
*)
(* caller *)
let rec evaluate_eterm eterm env =
  let (h,termss) = decompose_eterm eterm in
  match h with
  | ENT(f,ity,ntyid) ->
      begin try
        let (vte,body) =
          try Hashtbl.find tracetab (f,ity) with Not_found ->
            register_backchain f ity ntyid;
            Hashtbl.find tracetab (f,ity)
        in
        let (vte',body') = rename_vte_eterm vte body in
        let env' = mk_env vte' termss in
        evaluate_eterm body' (env'@env)
      with Not_found -> assert false end
  ...
```
</details><!--}}}-->

<a name = "Conversion__pterm2term"></a>
Conversion.pterm2term
---------------------

````ocaml
let rec pterm2term vmap pterm =
  match pterm with
    Syntax.PTapp(h, pterms) ->
      let h' =
        match h with
        | Syntax.Name(s) -> (try Var(List.assoc s vmap) with Not_found -> T(s))
        | Syntax.NT(s) -> NT(lookup_ntid s)
        | Syntax.FUN(_,_) -> assert false
        | Syntax.CASE(_n) -> assert false
        | Syntax.FD(_n) -> assert false
        | Syntax.PAIR -> assert false
        | Syntax.DPAIR -> assert false
      in
      ...
````

+ 全体の流れ
  + `Conversion.convert`
      + `elim_fun_from_*`がλ-liftingをする
          + `*`には prerule, preterm, head などが入る
      + `pterm2term`が何らかの変換をする
+ `elim_fun_from_*`を通った後は`Fun | CASE | FD | PAIR | DPAIR`にmatchしない
+ 問題点
  + ruleに対する述語「内部に表れる全てのheadがFUNなどにマッチしない」が現状表現できない
  + できたとして発見も難しそう


Scc.find_cycle
--------------

<details>

```ocaml
let rec find_cycle((g:graph),visited,x) =
  let nexts = try get_nexts g x with Not_found -> [] in
  let g' = find_cycle_next(g, x, x::visited, nexts) in
    delete_nodes g' [x]
and find_cycle_next(g, x, visited, nexts) =
  match nexts with
  | [] -> g
  | y::yl ->
      if List.mem y visited then
        raise Cycle
      else
        let g' = find_cycle(g, visited, y) in
          find_cycle_next(g', x, visited, yl);;
```

</details>

Listのソート
============

Pobdd.restrict_sorted
---------------------

```
let restrict_sorted t vl =
  let memo = ref Op1Map.empty in
  assert (sorted (List.map (function POS v | NEG v -> v) vl));
  ...
```

