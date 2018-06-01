
（未整理の問題）

<a name = "merge_tree"></a>
### Cegen.merge_tree

事前条件: 各パスπに対して，`t1(π)`と`t2(π)`の両方がNodeならばそのNodeのラベルが等しく，子の数も等しい．

<!-- 呼び出し元 evaluate_eterms が何をやっているか良くわからない -->

```ocaml
type tree = Node of string * tree list | Bottom
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
```

#### 案

+ labelが等しいという性質はrelational propertyに帰着
+ arityが等しいという性質は木のデータ構造にarityの情報を持たせることで対応

<a name = "mk_env"></a>
### Cegen.mk_env

```ocaml
let rec mk_env : ('a * 'b list) list -> 'c list list -> (('a * 'b) * 'c) list =
  fun vte termss ->
    match (vte, termss) with
      ([], []) -> []
    | ((v,ty)::vte', ts::termss') ->
         let x = List.combine ty ts in
          (List.map (fun (ity,t)->((v,ity),t)) x) @ (mk_env vte' termss')
    | _ -> assert false
(* 次の関数と同等(のはず) *)
let rec mk_env : ('a * 'b list) list -> 'c list list -> (('a * 'b) * 'c) list =
  fun vte termss ->
    try
      let aux (v,ty) ts =
        List.map2 (fun ity t -> ((v,ity),t)) ty ts
      in
        List.map2 aux vte termss |> List.concat
    with
      Invalid_argument _ -> assert false
```

説明の簡略化のため第一引数をunzipして `'a list -> 'b list list -> 'c list list -> (('a * 'b) * 'c) list`とみなして考える．
assert falseに到達しない条件は

1. `'a list`, `'b list list`, `'c list list`の長さが全て等しく
2. 各`i`に対して`'b list list`と`'c list list`の第`i`要素の長さが等しい

2番目の条件が難しい．

