
Invariantがどこで保証されているか特定できていない（あるいはできそうにない）
==========================================================================

Saturate.range_types
--------------------

  + `ty1 : ity list`の各要素が`ItyFun`にmatchする．
  + `ty1`は`ty_of_term`由来で，termを`App(t1,t2)`にmatchさせたときのt1のtyp
  + `App(t1,t2)` => `t1`は関数というinvariantは陽には得られないと思うので難しい

    <details><><!--{{{-->

    ```ocaml
    let range_types ty1 ty2 =
      List.fold_left
        begin fun ty ity1 ->
          match ity1 with
          | ItyFun(_,ty3,ity)->
              if List.for_all
                  (fun ity3-> List.exists (fun ity2-> subtype ity2 ity3) ty2)
                  ty3
              then add_ity ity ty
              else ty
          | _ -> assert false
        end
        [] ty1
    (* caller *)
    let rec ty_of_term venv term =
      match term with
      | NT(f) -> ty_of_nt f
      | T(a) -> ty_of_t a
      | Var(v) -> ty_of_var venv v
      | App(t1,t2) ->
          let ty1 = ty_of_term venv t1 in
          let ty2 = ty_of_term venv t2 in
          range_types ty1 ty2
    ```

    </details><!--}}}-->


  + 似ている関数
      + `Saturate.range_types_with_vte`

Cegen.evaluate_eterm
--------------------

TODO

<details><!--{{{-->

```ocaml
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
  | ET(a,_aty) ->
      begin try
        let trees = List.map (fun ts -> evaluate_eterms ts env) termss in
        Node(a, trees)
      with Not_found -> assert false end
  | EVar(v,aty) ->
      begin try
        let eterm1 = List.assoc (v,aty) env in
        evaluate_eterm (compose_eterm eterm1 termss) env
       with Not_found -> assert false end
  | ECoerce(aty1,aty2,t) ->
      begin try
        match (aty1,aty2) with
        | (ItyQ(q1),ItyQ(q2)) -> assert (q1=q2); evaluate_eterm t env
        | (ItyFun(_,ty11,aty11), ItyFun(_,ty21,aty21)) ->
            begin match termss with
            | [] -> assert false
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

</details><!--}}}-->

検証が恐らくできないもの
========================

AlternatingAutomaton.from_transition
------------------------------------

  + `let init = fst (fst (List.hd transitions)) in`
  + `transitions`はparserの返り値

AlternatingAutomaton.convert
----------------------------

  + 同上

