
+ `Ai.id2state`

    + `Hashtbl`のmember

+ `Ai.state2id`

    + `Hashtbl`のmember

+ `Ai.merge_statevecs`

    + non-nil
    + 検証できそう → [詳細](../likely_to_be_verified.md#aimerge_statevecs)

    + 呼び出し:

        + merge_statevecs ->
        + expand_states ->
        + expand_terminal ->
        + process_node（2箇所）

            + 1箇所目は

              ```ocaml
              if qs''=[] then (* states qs have been processed before *)
                ()
              else begin
                update_states_of_node node (merge_states qs' qs'');
                match h with
                | Ht(a) -> expand_terminal a termss qs''
                ...
              ```

            + 2箇所目は`dequeue()`の返り値を使っているので難しそう


+ `Ai.expand_varheadnode`

    + reference


+ `Ai.add_binding_st`

    + arrayと`List.assoc`

+ `Ai.register_newnode`

    + `Hashtbl`のmember

+ `Ai.term2head`

    + 検証できそう → [詳細](../likely_to_be_verified.md#aiterm2head)

+ `Ai.childnodes`

    + 呼び出し
        + process_node
        + expand
            + dequeue_node()の結果を渡しているので無理


+ `Ai.nt_in_term_with_linearity`

    + 検証できそう → [詳細](../likely_to_be_verified.md#aint_in_term_with_linearity)

+ `Cegen.mk_vte`

    + arityに関する推論．まだできない

+ `Cegen.mk_ehead`

    + 検証できそう → [詳細](../likely_to_be_verified.md#cegenmk_ehead)

+ `Cegen.lookup_headty`

    + `assert false`が二つ
    + 片方は検証できそう → [詳細](../likely_to_be_verified.md#cegenlookup_headty)

+ `Cegen.register_backchain`

    + `find_derivation`が`Not_found`を投げないことを示す必要があり難しい
        + 特に`List.iter`の辺り

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

            let rec find_derivation ntyid vte term aty =
              let (h,terms) = Grammar.decompose_term term in
              let k = List.length terms in
              let head_typings = find_headtype ntyid vte h aty k in
              try
                List.iter (fun (eh,aty0) -> (* ここ *)
                    try
                      let (eterms,rty) = find_derivation_terms ntyid vte terms aty0 in
                      let eterm1 = compose_eterm eh eterms in
                      let eterm2 =
                        if rty=aty then eterm1
                        else ECoerce(rty,aty,eterm1)
                      in raise (Found eterm2)
                    with Not_found -> ()
                  ) head_typings; raise Not_found
              with Found eterm -> eterm
          ```

+ `Cegen.mk_env`

    + caller
        + `evaluate_eterm`
            + `Hashtbl`を使うので難しい

+ `Cegen.merge_tree`

    + 難しい

+ `Cegen.evaluate_eterm`

    + `Hashtbl`など
    + 多くの`assert false`があるがどれも難しそう

+ `Cegen.string_of_path`
    + `find_ce`の返り値のterm`t`がpathになっていることを示す（難しい）

+ `Conversion.pterm2term`

    + 詳細

      ```ocaml
      let rec pterm2term vmap pterm =
        (* distinguish between variables and terminal symbols **)
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
            let terms = List.map (pterm2term vmap) pterms in
            let terms' = if !(Flags.normalize) then
                List.map normalize_term terms
              else terms
            in
            mk_app h' terms'

      let elim_fun_from_head vl h newrules =
        match h with
        | Syntax.Name(s) -> (Syntax.PTapp(Syntax.Name(s),[]), newrules)
        | Syntax.NT(s) -> (Syntax.PTapp(Syntax.NT(s),[]), newrules)
        | Syntax.FUN(vl1,pterm) ->
            let vl' = vl@vl1 in (* what if names in vl and vl1 clashe? *)
            let (pterm',newrules') = elim_fun_from_preterm vl' pterm newrules in
            let f = Syntax.new_ntname() in
            let pterms1 = List.map (fun v -> Syntax.PTapp(Syntax.Name(v), [])) vl in
            (Syntax.PTapp(Syntax.NT(f), pterms1), (f, vl', pterm')::newrules')
        | Syntax.CASE(_n) -> assert false
        | Syntax.FD(_n) -> assert false
        | Syntax.PAIR -> assert false
        | Syntax.DPAIR -> assert false

      let prerules2gram prerules =
        let prerules = elim_fun_from_prerules prerules in
        ...
        let _ = prerules2rules rules vinfo prerules in
        ...
      ```

      + `pterm2term`は`prerules2rules`内で呼ばれる
      + `elim_fun_from_head`は`elim_fun_from_prerules`内で呼ばれる
      + `elim_fun_from_head`を通った後なら`pterm2term`の`assert false`は踏まれないはずだが

+ `Conversion.elim_fun_from_head`

    + parserまで遡らないといけないはず．難しい

+ `Grammar.find_dep`
    + `List.assoc`

+ `Grammar.find_sc`
    + `List.find (List.mem _) _`

+ `Saturate.tyseq_mem`
    + `tyseq`系はデータ型の定義からして複雑すぎるので保留
    + (`type tyseq = TySeq of (Grammar.ty * (tyseq ref)) list | TySeqNil`)

+ `Saturate.range_types`

    + `ty1 : ity list`の要素が全部`ItyFun`にmatchする．
      `ty1`は`ty_of_term`由来で，termを`App(t1,t2)`にmatchさせたときのt1のtyp．
    + `ty1`の出処を追うと`Ai.id2state`で，この関数は`Hashtbl`を使っている

+ `Saturate.range_types_with_vte`
    + 上の関数のvariation．ほぼ同じ

+ `Saturate.ty_of_var`
    + 実質`List.find`なので難しい

+ `Saturate.split_ity`
    + `let (h, ts) = decompose_term t`のもとで`h`につく各型tyについて`length ts <= tyのarity`
        + 難しい

+ `Saturate.get_range`
    + 同上

+ `Saturate.ty_of_head`
  + 検証できそう → [詳細](../likely_to_be_verified#saturatety_of_head)
  + caller
      + `ty_of_term2`
          + `decompose_term`のパターン

+ `Saturate.ty_of_head_q`
  + 検証できそう → [詳細](../likely_to_be_verified#saturatety_of_head_q)
  + caller
      + `match_head_types` -> `check_ty_of_term` で`decompose_term`のパターンに

+ `Saturate.ty_of_head_q2`
  + 同上 → [詳細](../likely_to_be_verified#saturatety_of_head_q2)

+ `Saturate.get_argtys`
  + arityに関する推論．まだできない

+ `Saturate.check_args_aux`
  + `List.combine`と同じ条件だがcaller側が複雑
      + リストのtraverseに使われる

+ `Saturate.check_argtypes_aux`
  + 上のvariation

+ `Saturate.check_argtypes_inc_aux`
  + 上のvariation

+ `Saturate.tcheck_terms_w_venv`
  + 上のvariationというわけではないが同じような構造で難しい

+ `Saturate.tcheck_terms_wo_venv`
  + 同上

+ `Saturate.tcheck_terms_wo_venv_inc`
  + 同上

+ `Stype.arity2sty`
  + 検証できそう → [詳細](../likely_to_be_verified.md#stypearity2sty)
  + caller
      + `alpha2cste`
        直前で n < 0 でないことをcheckしているので行ける

+ `Type.lookup_cte`
  + `Hashtbl`
