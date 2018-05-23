
# HorSat2の分析

## 簡単な拡張が必要なもの

### 代数的データ構造のパターンマッチ

+ [Cegen.mk_ehead](./ADT.md#mk_ehead)
    + 単純

+ [Cegen.lookup_headty](./List.mem.md#lookup_headty)
    + List.memとの組み合わせ

+ [Ai.expand_varheadnode](./ADT.md#expand_varheadnode)
    + 参照との組み合わせ

+ Ai.term2head
    + 単純

+ Ai.childnodes
    + 単純

+ [Ai.nt_in_term_with_linearity](./ADT.md#nt_in_term_with_linearity)
    + Grammar.decompose_termと合わせる

## 本質的な拡張が必要なもの

### Reference, Hashtbl

+ [Conversion.register_nt](./Hashtbl.md#register_nt)
    + Hashtblのmembership
    + HorSat2への入力次第ではfailを避けられない

+ [Conversion.lookup_ntid](./Hashtbl.md#lookup_ntid)
    + Hashtblのmembership
    + HorSat2への入力次第ではfailを避けられない

+ Cegen.evaluate_eterm
    + TODO (assertionが沢山ある)

+ [Scc.take_from_visited](./Reference.md#take_from_visited)
    + `int list ref`へのmembership

+ [Ai.expand_varheadnode](./ADT.md#expand_varheadnode)
    + ADTとの組み合わせ

+ [Ai.add_binding_st](./List.mem.md#add_binding_st)
    + `List.assoc rho' (!binding_array_nt).(f)`
    + 難しそう

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
+ [Ai.add_binding_st](./List.mem.md#add_binding_st)
    + Referenceとの組み合わせ
    + `List.assoc rho' (!binding_array_nt).(f)`
    + TODO 難しそう

### List.exists

+ [Grammar.find_sc](./List.mem.md#find_sc)
    + `List.find (fun x -> List.mem f x) scc`
    + unionへのmembershipに帰着できる

+ [Saturate.ty_of_var](./List.mem.md#ty_of_var)

### 代数的データ型固有の述語

+ Conversion.pterm2term
    + 再帰的

+ Conversion.elim_fun_from_head
    + 再帰的

+ Cegen.mk_vte
    + arity

+ Saturate.split_ity
    + arity

+ Saturate.get_range
    + arity (同上)

+ Saturate.get_argtys
    + arity (同上)

+ Saturate.tyseq_mem
    + 参照 + 再帰もある

+ Saturate.tyseq_subsumed
    + 参照 + 再帰もある

+ Saturate.tyseq_merge_tys
    + 参照 + 再帰もある

+ Saturate.ty_of_head

+ Saturate.ty_of_headq

+ Saturate.ty_of_head

+ Cegen.merge_tree
    + どうするんだこれ
+ Cegen.string_of_path
    + どうするんだこれ(2)


### Array

arrayへのアクセス`arr.(i)`はindex out of bound例外を投げることを忘れていた．  
調べ直さないといけない

### 保留

+ Cegen.evaluate_eterm
+ Cegen.find_derivation
+ Cegen.mk_env
+ Pobdd.make_node

# 相互再帰の型



