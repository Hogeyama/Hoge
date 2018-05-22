
# HorSat2の分析

## 既に検証が通るもの

+ [Utilities.list_take_n](./work_well.md#list_take_n)

+ Utilities.list_repl

+ Utilities.list_take_n_and_rest

+ Utilities.list_rem_n


## 簡単な拡張が必要なもの

### 代数的データ構造のパターンマッチ

+ Cegen.mk_ehead
+ Cegen.lookup_headty
+ Ai.expand_varheadnode
    + 参照もある
+ Ai.term2head
+ Ai.childnodes
+ Ai.nt_in_term_with_linearity
    + Grammar.decompose_termと合わせる
+ Saturate.tyseq_mem
    + 参照+再帰もある
+ Saturate.tyseq_subsumed
    + 参照+再帰もある
+ Saturate.tyseq_merge_tys
    + 参照+再帰もある
+ Saturate.ty_of_head
+ Saturate.ty_of_headq
+ Saturate.ty_of_head


### Array


## 本質的な拡張が必要なもの

### Reference, Hashtbl

+ Conversion.register_nt
+ Conversion.lookup_ntid
+ Cegen.evaluate_eterm
+ Scc.take_from_visited
+ Ai.expand_varheadnode
+ Ai.add_binding_st
+ Ai.id2state
+ Ai.state2id
+ Ai.register_newnode
+ Saturate.tyseq_mem
    + ADT
+ Saturate.tyseq_subsumed
    + ADT
+ Saturate.tyseq_add_wo_subtyping
    + ADT
+ Saturate.tyseq_rem_subtyping_aux
    + ADT
+ Saturate.tyseq_merge_tys
    + ADT


### List.mem

+ [Scc.split_list_at](./List.mem.md#split_list_at)
    + 再帰
+ Grammar.find_dep
    + `List.assoc`を使うだけ
+ [Cegen.lookup_headty](./List.mem.md#lookup_headty)
    + ADTのパターンマッチと組み合わせ
+ [Ai.add_binding_st](./List.mem.md#)
    + `List.assoc rho' (!binding_array_nt).(f)`
    + 難しそう

### List.exists

+ [Grammar.find_sc](./List.mem.md#find_sc)
    + `List.find (fun x -> List.mem f x) scc`
    + unionへのmembershipに帰着できる

+ [Saturate.ty_of_var]
    + memではなくsatisfy

    ```
    let rec ty_of_var venv (f,i) =
      match venv with
      | [] -> assert false
      | (j1,j2,tys)::venv' ->
        if j1<=i && i<=j2 then
           proj_tys f (i-j1) tys
        else ty_of_var venv' (f,i)
    ```



### 代数的データ型固有の述語

+ Conversion.pterm2term
    + 再帰的
+ Conversion.elim_fun_from_head
    + 再帰的
+ Cegen.mk_vte
    + arity
+ Cegen.merge_tree
    + どうするんだこれ
+ Cegen.string_of_path
    + どうするんだこれ(2)
+ Saturate.split_ity
    + arity
+ Saturate.get_range
    + arity (同上)
+ Saturate.get_argtys
    + arity (同上)

### 保留

+ Cegen.evaluate_eterm
+ Cegen.find_derivation
+ Cegen.mk_env
+ Pobdd.make_node

# 相互再帰の型



