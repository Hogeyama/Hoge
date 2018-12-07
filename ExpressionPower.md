
ADT固有のmeasure，再帰的な述語他
================================

+ `Cegen.mk_vte`
    + arityを述語で表現する必要性

      <details><!--{{{-->

      ```ocaml
      type ity = ItyQ of ity_id | ItyFun of ity_id * ty * ity
      let rec arity = function
        | ItyQ(_) -> 0
        | ItyFun(_,_,ity) -> 1 + arity ity

      (*{SPEC}
      type mk_vte : (vars : int list) -> { at : ity | arity at >= List.length vars } -> _
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

      </details><!--}}}-->

+ `Cegen.merge_tree`
  + 木がmergeできる
      + Bottomと任意の木はmergeできる
      + Nodeどうしは次の条件を満たすときmergeできる
          + ラベルが等しく
          + 子の数が等しく
          + 対応する子がmergeできる

    <details>

    ```ocaml
    let rec merge_tree t1 t2 =
      match (t1,t2) with
      | (Bottom,_) -> t2
      | (_, Bottom) -> t1
      | (Node(a1,ts1),Node(a2,ts2)) ->
          if a1=a2 then
            Node(a1, merge_trees ts1 ts2)
          else assert false
    and merge_trees ts1 ts2 =
      List.map (fun (t1,t2)->merge_tree t1 t2) (List.combine ts1 ts2)
                                                ^^^^^^^^^^^^
    ```

    </details>

+ `Saturate.split_ity`
  + `let (h, ts) = decompose_term t`として`h`につく各型`ty`について `length ts <= tyのarity`
  + caller: `ty_of_term2`

    <details>

    ```ocaml
    let rec split_ity arity ity =
      if arity=0 then ([],ity)
      else match ity with
        | ItyFun(_,ty,ity1)->
            let (tys,ity') = split_ity (arity-1) ity1 in
            (ty::tys, ity')
        | _ -> assert false
    ```

    </details>


+ `Saturate.get_range`

  + `Saturate.split_ity`と大体同じ

    <details>

    ```ocaml
    let rec get_range ity arity =
      if arity=0 then ity
      else
        match ity with
        | ItyFun(_,_,ity1) -> get_range ity1 (arity-1)
        | _ -> assert false
    ```

    </details>

+ `Saturate.get_argtys`

  + 同上

    <details>

    ```ocaml
    let rec get_argtys arity ity =
      if arity=0 then []
      else
        match ity with
        | ItyFun(_,ty,ity1) -> ty::(get_argtys (arity-1) ity1)
        | _ -> assert false
    ```

    </details>

+ `Scc.find_cycle`

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

<a name = "Pobdd__make_node"></a>
+ `Pobdd.make_node`
  + `assert (node_id t1 <> node_id t2)`
  + caller
      + `bdd_var`, `bdd_nvar`, `neg`, `bdd_and`, `bdd_or`, `exists_vl`, `forall_vl`, `imp_and_exists`, `restrict_sorted`
      + `neg`以外は呼び出し前にcheckが入る (`if node_id t1 = node_id t2 then ... else make_node t1 t2`)
          + → 行けそう.mdに TODO
  + `neg`が問題

    <details>

    ```ocaml
    let node_id = function
      | Leaf(true) -> 0
      | Leaf(false) -> 1
      | Node(_,_,_,x,_) -> x;;
    let make_node (v,t1,t2) =
      let i1 = node_id t1 in
      let i2 = node_id t2 in
      let key = (v,i1,i2) in
      assert (i1 <> i2);
      ^^^^^^^^^^^^^^^^^^
      try
        NodeHash.find node_hashtbl key
      with Not_found -> begin
        let i = gen_id () in
        let l1 = bdd_vars t1 in
        let l2 = bdd_vars t2 in
        let l = merge_vars l1 l2 in
        let t = Node (v,t1,t2,i,v::l) in
        NodeHash.add node_hashtbl key t;
        t
      end;;
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

    </details>

+ `Cegen.mk_env`
  + リストの長さについて複雑な条件
  + callerもHashtblが絡んでくるので難しい

    <details>

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
    </details>

<a name = "Conversion__pterm2term"></a>
+ `Conversion.pterm2term`周り

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

