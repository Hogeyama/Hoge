
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

Saturate.check_args_aux
-----------------------

  + リストの長さが同じという条件がどこで保証されているのか追うのが大変
      + リストの長さが同じリスト？
          <!-- + TODO ADT.mdに移動したほうがよいか -->

    <details><!--{{{-->

    ```ocaml
    let rec check_args_aux tys terms venv =
      match (tys,terms) with
      | ([], []) -> true
      | (ty::tys', t::terms') ->
          List.for_all (fun ity-> check_term t ity venv) ty
            && check_args_aux tys' terms' venv
      | _ -> assert false
             ^^^^^^^^^^^^ tysとtermsの長さが同じ
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
      | _ -> (* ItyFun *)
          let q = codom_of_ity ity in
          let ty = List.filter
              (fun ity1 -> subtype (get_range ity1 arity) ity)
              (ty_of_head_q2 h venv q) in
          List.map (fun ity -> get_argtys arity ity) ty
    ```

    </details><!--}}}-->

  + 似ている関数
        + `Saturate.check_argtypes_aux`

        + `Saturate.check_argtypes_inc_aux`

        + `Saturate.tcheck_terms_w_venv`

        + `Saturate.tcheck_terms_wo_venv`

        + `Saturate.tcheck_terms_wo_venv_inc`

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

