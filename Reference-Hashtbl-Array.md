
Reference, Array, Hashtbl

Reference
=========

Ai.expand_varheadnode
---------------------

````ocaml
let expand_varheadnode term (node: node ref) =
  let (aterm,qs) = !node in
  let (h,termss) = aterm in
  match h with
  | Hvar(_x) ->
      let (h',terms)=term in
      enqueue_node ((h', terms@termss),qs)
  | _ -> assert false
````

`node`はグローバル変数(`tab_variableheadnode : node ref list array array ref`)由来


<a name = "Ai__merge_statevecs"></a>
Ai.merge_statevecs
------------------

Listの non-emptiness

```ocaml
let rec merge_statevecs qsvecs =
  match qsvecs with
  | [] -> assert false
          ^^^^^^^^^^^^
  | [qsvec] -> qsvec
  | qsvec1::qsvecs' ->
      merge_statevec qsvec1 (merge_statevecs qsvecs')

(* caller *)
let expand_states qs a =
  merge_statevecs (List.map (fun q -> expand_state q a) qs)
  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ qsがnon-empty

(* caller of expand_states *)
let expand_terminal a termss qs =
  let aterms = termss in
  let qss = expand_states qs a in
            ^^^^^^^^^^^^^^^^^^ qsがnon-empty
  let aterms' = Utilities.indexlist aterms in
  List.iter (fun (i,aterm) -> if qss.(i)=[] then () else enqueue_node (aterm, qss.(i))) aterms'

(* caller of expand_terminal *)
let process_node (aterm,qs) =
  let (h, termss) = decompose_aterm aterm in
  match lookup_nodetab aterm with
  | Some(node) -> ...
  | None -> (* aterm has not been processed *)
      let node = register_newnode (aterm,qs) in
      match h with
      | Ht(a) -> expand_terminal a termss qs
                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^
      ...

(* caller of process_node *)
let rec expand() =
  match dequeue_node() with
        ^^^^^^^^^^^^^^
  | None -> print_string ("size of ACG: "^(string_of_int (ATermHashtbl.length nodetab))^"\n")
  | Some(aterm,qs) -> process_node(aterm,qs); expand()
                      ^^^^^^^^^^^^^^^^^^^^^^
```
[同じ関数の別呼び出しで簡単に検証可能な方](./Possible.md#Ai__merge_statevecs)

Referenceから取り出したリストがnon-empty
`Ai.nodequeue : (aterm * int list) list ref`の`int list`が常にnon-emptyであることを保証すればよい．
`Ai.nodequeue`に書き込みをする関数は次の二つ:

```
let enqueue_node node = nodequeue := node::!nodequeue
let dequeue_node () = match !nodequeue with
  | [] -> None
  | x::q -> (nodequeue := q; Some(x))
```

`enqueue_node`のcallerは`process_node`, `init_expansion`, `expand_terminal`, `expand_varheadnode`の4つで，
どれも局所的な推論によって書き込むリストがnon-emptyであることを示せる
（`expand_terminal`だけは`if qss.(i)=[] then () else enqueue_node (aterm, qss.(i))) aterms'`という風に配列が関わるので工夫が要る）．


<!--
Setqueue.dequeue
----------------

  ````ocaml
  let rec dequeue (qref,bitmap) =
    match !qref with
    | [] -> raise Empty
    | n::ns ->
        qref := ns;
        if bitmap.(n)
        then (bitmap.(n) <- false; n)
        else dequeue(qref,bitmap)
  ````
全部catchされる
-->

Cegen.find_ce
--------------

+ `let (_,ntyid) = List.hd ((!nteallref).(0).(0)) in`
+ 初期化(`Cegen.init_nte()`)時には`(!nteallref).(0).(0)`は空なのでtemporalな推論が必要
    + 非決定的な値とみなす方法ではできない


他
--

+ `type tyseq = TySeq of (Grammar.ty * (tyseq ref)) list | TySeqNil`に関するエラー
  + `Saturate.tyseq_mem`
  + `Saturate.tyseq_subsumed`
  + `Saturate.tyseq_add_wo_subtyping`
  + `Saturate.tyseq_rem_subtyping_aux`
  + `Saturate.tyseq_merge_tys`

Array
=====

+ `Ai.add_binding_st`
  + `try List.assoc rho' (!binding_array_nt).(f) with Not_found -> assert false in`

+ `Cegen.find_ce`
  + `let (_,ntyid) = List.hd ((!nteallref).(0).(0)) in`

+ `Saturate.register_terms_te`
  + `let tyseqref = (!terms_te).(id) in ... let tys = List.hd (tyseq2tyss !tyseqref 0) in`
  + `tyseq2tyss`が複雑なので難しい

+ `Utilities.list_max`
  + `f c (List.tl l) (List.hd l)`
  + callerでArrayを使っている

    ```
    let order_of_nste nste =
      let nste' = indexlist (Array.to_list nste) in
      let ordmap = List.map (fun (nt, sty) -> (nt, order_of_sty sty)) nste' in
      let x = list_max (fun (_nt1,ord1) ->fun (_nt2,ord2) -> compare ord1 ord2) ordmap in
      x

    (* order_of_nste の caller *)
    let tcheck g alpha =
      ...
      let num_of_nts = Array.length g.nt in
      let nste = Array.make num_of_nts dummy_type in
      ...
      let (f,ord) = order_of_nste nste in
      ...
    ```

    `Array.length g.nt > 0`の証明は難しい:
    + `g`は`Conversion.convert(_ata)`由来（`Main.verifyParseResult`参照）
    + conversion.mlを見るとどうやら`g.nt`のサイズはパース結果のprerulesの長さに等しい？

Hashtbl
=======

+ `Ai.id2state`
+ `Ai.state2id`
+ `Ai.register_newnode`
+ `Type.lookup_cte`

<a name = "cegenevaluate_eterm"></a>
+ `Cegn.evaluate_eterm`
    + `mk_env vte' termss`を呼ぶときに`vte'`と`termss`の長さが同じである必要がある

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
        ...
      let rec mk_env vte termss =
        match (vte, termss) with
        | ([], []) -> []
        | ((v,ty)::vte', ts::termss') ->
            let x = List.combine ty ts in
            List.map (fun (ity,t)->((v,ity),t)) x@(mk_env vte' termss')
        | _ -> assert false

      ```

      </details><!--}}}>

