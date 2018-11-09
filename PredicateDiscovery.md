
+ `Cegen.string_of_path`

    <details><sumarry>code</summary><!--{{{-->

    ```ocaml
    (*{SPEC}
    type string_of_path : { t : tree | t <> Bottom } -> string
    {SPEC}*)
    let rec string_of_path t =
      match t with
      | Node(a,tl) ->
          let (i,t') = find_nonbot tl 1 in
          if i=0 then ("("^a^",0)")
          else ("("^a^","^(string_of_int i)^")"^(string_of_path t'))
      | _ -> assert false
    (*{SPEC}
    type find_nonbot
      :  tree list
      -> { i : int | i > 0 }
      -> { (j,t) : int * tree | t = Bottom => j = 0 }
    {SPEC}*)
    let rec find_nonbot tl i =
      match tl with
      | [] -> (0, Bottom)
      | t::tl' ->
          match t with
          | Bottom -> find_nonbot tl' (i+1)
          | Node(_,_) -> (i, t)
    ```

    </details><!--}}}-->

+ `Saturate.range_types`
  + `ty1 : ity list`の各要素が`ItyFun`にmatchする．
  + `ty1`は`ty_of_term`由来で，termを`App(t1,t2)`にmatchさせたときのt1のtyp
  + `App(t1,t2)` => `t1`は関数というinvariantは陽には得られないと思うので厳しいか

    <details><sumarry>code</summary><!--{{{-->

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

+ `Saturate.range_types_with_vte`
  + 上の関数のvariation．ほぼ同じ

+ `Saturate.check_args_aux`
  + `List.combine`と同じ条件だがcaller側が複雑
      + xssのすべての要素xsは，その長さがysの長さと等しい

    <details><sumarry>code</summary><!--{{{-->

    ```ocaml
    let rec check_args tys_ity_list terms venv ty =
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
    and check_args_aux tys terms venv =
      match (tys,terms) with
      | ([], []) -> true
      | (ty::tys', t::terms') ->
          List.for_all (fun ity-> check_term t ity venv) ty
            && check_args_aux tys' terms' venv
      | _ -> assert false
             ^^^^^^^^^^^^
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
    ```

    </details><!--}}}-->


+ `Saturate.check_argtypes_aux`
  + 上のvariation

+ `Saturate.check_argtypes_inc_aux`
  + 上のvariation

+ `Saturate.tcheck_terms_w_venv`
  + 上のvariationではないが，同じような構造

+ `Saturate.tcheck_terms_wo_venv`
  + 同上

+ `Saturate.tcheck_terms_wo_venv_inc`
  + 同上

+ `Cegen.evaluate_eterm`
  + わちゃわちゃしている

    <details><sumarry>code</summary><!--{{{-->

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
          with Not_found -> assert false end (* ここには来ないのでは？ *)
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

<!--
+ `Pobdd.make_node`
  + 詳細 → [link](./ExpressionPower.md#Pobdd__make_node)
-->

+ `AlternatingAutomaton.from_transition`
  + `let init = fst (fst (List.hd transitions)) in`
  + `transitions`はparserの返り値

+ `AlternatingAutomaton.convert`
  + 同上

+ `Utilities.list_max`
  + リストが空でないことを示す必要: `f c (List.tl l) (List.hd l)`
  + callerが難しい

    ```ocaml
    let order_of_nste nste =
      let nste' = indexlist (Array.to_list nste) in
      let ordmap = List.map (fun (nt, sty) -> (nt, order_of_sty sty)) nste' in
      let x = list_max (fun (_nt1,ord1) ->fun (_nt2,ord2) -> compare ord1 ord2) ordmap in
      x
    ```

+ `Cegen.evaluate_eterm`

+ `Cegen.find_derivation`

