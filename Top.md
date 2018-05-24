
# HorSat2の分析

## 簡単な拡張が必要なもの

### 代数的データ型(ADT)のパターンマッチ

述語の中でパターンマッチができればよいもの．

```ocaml
type foo = Foo of int | Bar of bool
```

に対して次のようなrefinement typeが書ける必要がある．

```
{ f : foo | is_Foo f && un_Foo f > 0 ||
            is_Bar f && not (un_Bar f) }
```

| 関数名 | コメント |
|--------|----------|
| [Cegen.mk_ehead](./ADT_easy.md#mk_ehead) | 単純 |
| [Cegen.lookup_headty](./List.mem.md#lookup_headty) | List.memとの組み合わせ |
| [Ai.expand_varheadnode](./ADT_easy.md#expand_varheadnode) | 参照との組み合わせ（deref後にパターンマッチする） |
| Ai.term2head | |
| Ai.childnodes | |
| [Ai.nt_in_term_with_linearity](./ADT_easy.md#nt_in_term_with_linearity) | |

## 本質的な拡張が必要なもの

### List.mem

| 関数名 | コメント |
|--------|----------|
| [Scc.split_list_at](./List.mem.md#split_list_at) | 再帰 |
| Grammar.find_dep | `List.assoc`を使うだけ |
| [Cegen.lookup_headty](./List.mem.md#lookup_headty) | ADTのパターンマッチと組み合わせ |
| [Ai.add_binding_st](./List.mem.md#add_binding_st) | Referenceとの組み合わせ: `List.assoc rho' (!binding_array_nt).(f)` |

### List.exists

| 関数名 | コメント |
|--------|----------|
| [Grammar.find_sc](./List.mem.md#find_sc) | `List.find (List.mem f)`に相当, unionへのmembershipに帰着できそう |
| [Saturate.ty_of_var](./List.mem.md#ty_of_var) | `List.find (fun (i,j) -> (i < k && k < j))`に相当 |

### Reference, Hashtbl

| [Conversion.register_nt](./Hashtbl.md#register_nt) | Hashtblのmembership. [^1] |
| [Conversion.lookup_ntid](./Hashtbl.md#lookup_ntid) | Hashtblのmembership. [^1] |
| Cegen.evaluate_eterm | TODO (assertionが沢山ある) |
| [Scc.take_from_visited](./Reference.md#take_from_visited) | `int list ref`へのmembership |
| [Ai.expand_varheadnode](./ADT_easy.md#expand_varheadnode) | ADTとの組み合わせ |
| [Ai.add_binding_st](./List.mem.md#add_binding_st) | `List.assoc rho' (!binding_array_nt).(f)`. 難しそう |
| Ai.id2state | Hashtblの単純なmembership |
| Ai.state2id | Hashtblの単純なmembership |
| Ai.register_newnode | Hashtblの単純なmembership |
| Saturate.tyseq_mem | [難しい方のADT](#代数的データ型固有の述語)との組み合わせ |
| Saturate.tyseq_subsumed | [^2] |
| Saturate.tyseq_add_wo_subtyping ||
| Saturate.tyseq_rem_subtyping_aux ||
| Saturate.tyseq_merge_tys ||

[^1]: HorSat2への入力次第ではfailを避けられない
[^2]: [代数的データ型固有の述語](#代数的データ型固有の述語)との組み合わせ

### 代数的データ型固有の述語

たとえば

```
type ity = ItyQ of state
         | ItyFun of a * b * ity
```

という型に対して

```
arity = function
        | ItyQ(_) -> 0
        | ItyFun(_,_,aty) -> 1 + arity aty
```

という関数を使わないと仕様が書けないケースがある．そのようなものをここで扱う．

+ [Cegen.mk_vte](./ADT_difficult.md#mk_vte)
    + arity

+ Conversion.pterm2term

+ Conversion.elim_fun_from_head

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

### Array

arrayへのアクセス`arr.(i)`はindex out of bound例外を投げることを忘れていた．
調べ直さないといけない

### TODO

+ Cegen.evaluate_eterm
+ Cegen.find_derivation
+ Cegen.merge_tree
+ Cegen.string_of_path
+ Cegen.mk_env
+ Pobdd.make_node



<!--# 相互再帰の型-->



