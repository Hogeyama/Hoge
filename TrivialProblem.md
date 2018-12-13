
<a name = "Main__report_breakdown"></a>
Main.report_breakdown
---------------------

```ocaml
let report_breakdown start_t end_t =
  let ts = List.rev !times in
  let last = if !times=[] then start_t else List.hd !times in
                                            ^^^^^^^^^^^^^^
  let start = ref start_t in
  List.iter
    (fun t ->
      print_string ("  checkpoint: "^(string_of_float (t -. !start))^"sec\n");
      start := t)
    ts;
  print_string ("  checkpoint: "^(string_of_float (end_t -. last))^"sec\n")
```

次のように書き換えれば今のMoCHiで検証可能

```ocaml
let report_breakdown start_t end_t =
  let ts = !times in
  let last = if ts=[] then start_t else List.hd ts in
                                        ^^^^^^^^^^
  let start = ref start_t in
  List.iter
    (fun t ->
      print_string ("  checkpoint: "^(string_of_float (t -. !start))^"sec\n");
      start := t)
    (List.rev ts);
  print_string ("  checkpoint: "^(string_of_float (end_t -. last))^"sec\n")
```

List.combine
============

<a name = "Utilities__inexlist"></a>
Utilities.indexlist
-------------------

```ocaml
let indexlist l =
  let len = List.length l in
  let indices = fromto 0 len in
  List.combine indices l

let indexlistr l =
  let len = List.length l in
  let indices = fromto 0 len in
  List.combine l indices
```

+ 述語発見がうまくいっていない
  TODO: うまく行かない原因調べる

<a name = "Ai__mk_trtab"></a>
Ai.mk_trtab
--------------

```ocaml
let mk_trtab m =
  register_state m.init;
  List.iter register_state m.st;
  let tr = m.delta in
  Hashtbl.clear trtab;
  List.iter (fun ((q,a),qs) ->
    let arity = List.length qs in
    let x = Array.make arity [] in
    let indices = fromto 0 arity in
    List.iter
      (fun (i,q') -> x.(i) <- [state2id q'])
      (List.combine indices qs);
       ^^^^^^^^^^^^^^^^^^^^^^^
    Hashtbl.add trtab (state2id q,a) x
  ) tr
```

[indexlist](#Utilities__inexlist)と同様

<a name = "Conversion__normalize_term"></a>
Conversion.normalize_term
-------------------------

```ocaml
let rec normalize_term term =
  match term with
  | App(_,_) ->
      if depth_of_term term > !(Flags.normalization_depth) then
        let vars = vars_in_term term in
        let arity = List.length vars in
        let nt = new_ntaux() in
        let subst = List.combine vars (List.map (fun i->Var(nt,i)) (fromto 0 arity)) in
                    ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
        let term' = Grammar.subst_term subst term in
        (register_new_rule nt arity term';
         mk_app (NT(nt)) (List.map (fun i-> Var i) vars))
      else term
  | _ -> term
```

[indexlist](#Utilities__inexlist)と同様

List Nonempty
=============

<a name = "Ai__merge_statevecs"></a>
Ai.merge_statevecs
------------------

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
  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

(* caller of expand_states *)
let expand_terminal a termss qs =
  let aterms = termss in
  let qss = expand_states qs a in
            ^^^^^^^^^^^^^^^^^^
  let aterms' = Utilities.indexlist aterms in
  List.iter (fun (i,aterm) -> if qss.(i)=[] then () else enqueue_node (aterm, qss.(i))) aterms'

(* caller of expand_terminal *)
let process_node (aterm,qs) =
  let (h, termss) = decompose_aterm aterm in
  match lookup_nodetab aterm with
  | Some(node) -> (* aterm has been processed before *)
      begin
        let qs' = states_of_node node in
        let qs'' = diff_states qs qs' in
        if qs''=[] then (* states qs have been processed before *)
          ()
        else begin
          update_states_of_node node (merge_states qs' qs'');
          match h with
          | Ht(a) -> expand_terminal a termss qs''
                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ (* ここはnil-checkしてあるのでsafe *)
          ...
        end
      end
  | None -> (* aterm has not been processed *)
      let node = register_newnode (aterm,qs) in
      match h with
      | Ht(a) -> expand_terminal a termss qs
                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^ (* こっちは厳しい*)
      ...
```

[同じ関数の別呼び出しで難しい方](./Reference-Hashtbl-Array.md#Ai__merge_statevecs)

他
==

`Cegen.string_of_path`
----------------------

```ocaml
(*{SPEC}
type string_of_path : { t : tree | match t with Bottom -> false | _ -> true } -> string
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
  -> { (j,t) : int * tree | match t with Bottom -> j = 0 | _ -> true }
{SPEC}*)
let rec find_nonbot tl i =
  match tl with
  | [] -> (0, Bottom)
  | t::tl' ->
      match t with
      | Bottom -> find_nonbot tl' (i+1)
      | Node(_,_) -> (i, t)
```

+ 今のmochiは`type tree = Bottom | Node of int * tree list`が扱えない（`tree list`の部分）
    + 実装上の問題

<a name = "Pobdd__make_node"></a>
Pobdd.make_node
---------------

  + `assert (node_id t1 <> node_id t2)`
  + caller
      + `bdd_var`, `bdd_nvar`, `neg`, `bdd_and`, `bdd_or`, `exists_vl`, `forall_vl`, `imp_and_exists`, `restrict_sorted`
      + `neg`以外は呼び出し前にチェックが入る (`if node_id t1 = node_id t2 then ... else make_node t1 t2`)
          + `neg`については[ここ](./ExpressionPower.md#Pobdd__make_node)

  + 検証
      + `bdd_var`, `bdd_nvar`は検証できた
      + `bdd_and`, `bdd_or`, `exists_vl`, `forall_vl`, `imp_and_exists`, `restrict_sorted`は自分のPCではabstractでメモリを使い果たしたため分からず

    <details>

    ```ocaml
    type bdd = Node of var * bdd * bdd * id * var list | Leaf of bool;;
    let node_id = function
      | Leaf(true) -> 0
      | Leaf(false) -> 1
      | Node(_,_,_,x,_) -> x

    let make_node (v,t1,t2) =
      let i1 = node_id t1 in
      let i2 = node_id t2 in
      assert (i1 <> i2);
      ...

    let bdd_true  = Leaf true
    let bdd_false = Leaf false
    let bdd_var v = make_node (v, bdd_true, bdd_false)

    let bdd_and t1 t2 =
      let memo = ref Op2Map.empty in
      let rec go t1 t2 = match (t1,t2) with
        | (Leaf b,t2) -> if b then t2 else bdd_false
        | (t1,Leaf b) -> if b then t1 else bdd_false
        | (Node (v1,x1,y1,i1,_), Node (v2,x2,y2,i2,_)) ->
          if Op2Map.mem (i1,i2) !memo then Op2Map.find (i1,i2) !memo
          else begin
            let (z,x1,x2,y1,y2) = match (Elt.compare v1 v2) with
              | 0 -> (v1,x1,x2,y1,y2)
              | x when x < 0 -> (v1,x1,t2,y1,t2)
              | _ -> (v2,t1,x2,t1,y2)
            in
            let t1' = go x1 x2 in
            let t2' = go y1 y2 in
            let t =
              if node_id t1' = node_id t2' then t1'
              else make_node (z,t1',t2') in
            memo := Op2Map.add (i1,i2) t !memo;
            t
          end
      in go t1 t2
    ```

    (8ケース)

    </details>

