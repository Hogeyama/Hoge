
+ `Ai.id2state`

    + `Hashtbl`のmember

+ `Ai.state2id`

    + `Hashtbl`のmember

+ `Ai.merge_statevecs`

    + non-nil
    + 検証できそう → [](../can_be_verified.md#Ai__merge_statevecs)

    + 呼び出し:

        + merge_statevecs ->
        + expand_states ->
        + expand_terminal ->
        + process_node（2箇所）

            + 1箇所目は

              ```
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

    + referenceから


+ `Ai.add_binding_st`

    + arrayと`List.assoc`

+ `Ai.register_newnode`

    + `Hashtbl`のmember

+ `Ai.term2head`

    + 検証できそう → [](../can_be_verified.md#Ai__term2head)

+ `Ai.childnodes`

    + 呼び出し
        + process_node
        + expand
            + dequeue_node()の結果を渡しているので無理


+ `Ai.nt_in_term_with_linearity`

    + 検証できそう → [](../can_be_verified.md#Ai__nt_in_term_with_linearity)
    + decompose_termの直後に呼んでいるので

+ `Cegen.mk_vte`

    + arityに関する推論．まだできない

+ `Cegen.mk_ehead`

    + 検証できそう → [](../can_be_verified.md#mk_ehead)

+ `Cegen.lookup_headty`

    + `Var(x)`の方
        + List.assoc
    + `_`の方
        + `Cegen.mk_ehead`と同じ
        + 検証できそう

+ `Cegen.register_backchain`

    + `find_derivation`が`Not_found`を投げないことを示すのは難しい
        + 特に`List.iter`の辺り

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

    + `elim_fun_*`を通れば`pterm2term`のassert falseは踏まないはずだが…

    + 詳細

      ```
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

    + parserまで遡らないといけない？

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
  + 検証できそう → [](../can_be_verified#Saturate__ty_of_head)
  + caller
      + `ty_of_term2`
          + `decompose_term`のパターン

+ `Saturate.ty_of_head_q`
  + 検証できそう → [](../can_be_verified#Saturate__ty_of_head_q)
  + caller
      + `match_head_types` -> `check_ty_of_term` で`decompose_term`のパターンに

+ `Saturate.ty_of_head_q2`
  + 同上 → [](../can_be_verified#Saturate__ty_of_head_q2)

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
  + 検証できそう → [](../can_be_verified.md#Stype__arity2sty)
  + caller
      + `alpha2cste`
        直前で n < 0 でないことをcheckしているので行ける

+ `Type.lookup_cte`
  + `Hashtbl`

