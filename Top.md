
# HorSat2の分析

## 簡単な拡張が必要なもの

### 代数的データ型(ADT)のパターンマッチ

述語の中でパターンマッチができればよいもの．

```ocaml
type foo = Foo of int | Bar of bool
```

に対して次のようなrefinement typeが書ければよい．

```
{ f : foo | is_Foo f && un_Foo f > 0 ||
            is_Bar f && not (un_Bar f) }
```

| 関数名 | コメント |
|--------|----------|
| [Cegen.mk_ehead](./ADT_easy.md#mk_ehead) | 単純 |
| [Cegen.lookup_headty](./List.md#lookup_headty) | List.memとの組み合わせ |
| [Ai.expand_varheadnode](./ADT_easy.md#expand_varheadnode) | 参照との組み合わせ（deref後にパターンマッチする） |
| Ai.term2head | 単純 |
| Ai.childnodes | 単純 |
| [Ai.nt_in_term_with_linearity](./ADT_easy.md#nt_in_term_with_linearity) | |
| Saturate.ty_of_head | 単純 |
| Saturate.ty_of_headq | 単純 |
| Saturate.ty_of_head | 単純 |

<!--
ty_of_* は ty_of_var(ヤバイ)を呼ぶが
ただ呼ぶだけなので問題視しないで良いはず
-->

## 本質的な拡張が必要なもの

### List.mem

`List.mem`や`List.mem_assoc`．Set theoryを入れる

| 関数名 | コメント |
|--------|----------|
| [Scc.split_list_at](./List.md#split_list_at) | 再帰 |
| Grammar.find_dep | `List.assoc`を使うだけ |
| [Cegen.lookup_headty](./List.md#lookup_headty) | ADTのパターンマッチと組み合わせ |
| [Ai.add_binding_st](./List.md#add_binding_st) | Referenceとの組み合わせ: `List.assoc rho' (!binding_array_nt).(f)` |

### List.exists

| 関数名 | コメント |
|--------|----------|
| [Grammar.find_sc](./List.md#find_sc) | `List.find (List.mem f)`に相当, unionへのmembershipに帰着できそう |
| [Saturate.ty_of_var](./List.md#ty_of_var) | `List.find (fun (i,j) -> (i < k && k < j))`に相当 |

### Reference, Hashtbl

| 関数名 | コメント |
|--------|----------|
| [Conversion.register_nt](./Hashtbl.md#register_nt) | Hashtblのmembership. \*1 |
| [Conversion.lookup_ntid](./Hashtbl.md#lookup_ntid) | Hashtblのmembership. \*1 |
| Cegen.evaluate_eterm | TODO (assertionが沢山ある) |
| [Scc.take_from_visited](./Reference.md#take_from_visited) | `int list ref`へのmembership |
| [Ai.expand_varheadnode](./ADT_easy.md#expand_varheadnode) | ADTとの組み合わせ |
| [Ai.add_binding_st](./List.md#add_binding_st) | `List.assoc rho' (!binding_array_nt).(f)`. 難しそう |
| Ai.id2state | Hashtblの単純なmembership |
| Ai.state2id | Hashtblの単純なmembership |
| Ai.register_newnode | Hashtblの単純なmembership |
| [Saturate.tyseq_mem](./ADT_difficult.md#tyseq_mem) | [代数的データ型固有の述語](#代数的データ型固有の述語)との組み合わせ |
| Saturate.tyseq_subsumed | 同上 |
| Saturate.tyseq_add_wo_subtyping | 同上 |
| Saturate.tyseq_rem_subtyping_aux | 同上 |
| Saturate.tyseq_merge_tys | 同上 |

\*1: HorSat2への入力次第ではfailを避けられない  

### 代数的データ型固有の述語

たとえば

```
(* grammer.ml *)
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

| 関数名 | コメント |
|--------|----------|
| [Cegen.mk_vte](./ADT_difficult.md#mk_vte) | arity |
| Saturate.split_ity | 同上 |
| Saturate.get_range | 同上  |
| Saturate.get_argtys | 同上 |
| [Saturate.tyseq_mem](./ADT_difficult.md#tyseq_mem) | 参照と再帰も関係する．難しそう |
| Saturate.tyseq_subsumed | 同上 |
| Saturate.tyseq_merge_tys | 同上 |
| [Conversion.pterm2term](./ADT_difficult.md#pterm2term) | |
| Conversion.elim_fun_from_head | pterm2termと似ている |

### Array

arrayへのアクセス`arr.(i)`はindex out of bound例外を投げることを忘れていたので調べ直します．

### TODO

+ Cegen.evaluate_eterm
+ Cegen.find_derivation
+ Cegen.merge_tree
+ Cegen.string_of_path
+ Cegen.mk_env
+ Pobdd.make_node

<!--# 相互再帰の型-->



