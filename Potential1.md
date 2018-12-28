
自動化できそうな変換によって検証できる形に落とし込めるケース

List Non-empty
==============

<a name = "Main__report_breakdown"></a>
Main.report_breakdown
---------------------

```ocaml
let times : float list ref = ref []

let report_breakdown start_t end_t =
  let ts = !times in
  let last = if ts=[] then start_t else List.hd ts in
  let start = ref start_t in
  List.iter
    (fun t ->
      print_string ("  checkpoint: "^(string_of_float (t -. !start))^"sec\n");
      start := t)
    (List.rev ts);
  print_string ("  checkpoint: "^(string_of_float (end_t -. last))^"sec\n")
```

+ 使われていない関数，moduleを削除すれば検証できる．
+ 上のコード片をMoCHiに渡せば検証が通る:

```
MoCHi: Model Checker for Higher-Order Problems
  Build: _b889e4e (after 2018-12-17 20:48:51 +0900)
  Z3 library version: 4.7.1.0
  HorSat2 version: 0.94
  HoIce version: 1.7.1
  OCaml version: 4.03.0
  Command: mochi-improve_encode_rec break.ml

（中略）

Safe!

CEGAR-cycles: 1
total: 0.421 sec
  abst: 0.292 sec
  mc: 0.007 sec
  refine: 0.000 sec
```

<details><!--{{{-->

```ocaml

open Utilities
     ^^^^^^^^^ Unknown modules
open Grammar
open Automaton
open Flags

let parseFile filename =
  let in_strm =
    try
      open_in filename
    with
        Sys_error _ -> (print_string ("Cannot open file: "^filename^"\n");exit(-1)) in
  let _ = print_string ("analyzing "^filename^"...\n") in
  let _ = flush stdout in
  let lexbuf = Lexing.from_channel in_strm in
               ^^^^^^ Unknown modules
  let result =
    try
      Parser.main Lexer.token lexbuf
    with
      | Failure _ -> exit(-1) (*** exception raised by the lexical analyer ***)
      | Parsing.Parse_error -> (print_string "Parse error\n";exit(-1)) in
  let _ =
    try
      close_in in_strm
    with
      Sys_error _ -> (print_string ("Cannot close file: "^filename^"\n");exit(-1))
  in
    result

let report_input g m =
  let () = if !(Flags.debugging) then print_gram g in
                                      ^^^^^^^^^^ Unknown function
  let () = print_string ("The number of rewrite rules: "^(string_of_int (Array.length g.r))^"\n") in
  let () = print_string ("The size of recursion scheme: "^(string_of_int (Grammar.size_of g))^"\n") in
  let () = print_string ("The number of states: "^(string_of_int (Automaton.size_st m))^"\n") in
    ()
```

これらを誤魔化す必要がある
+ mliだけ渡すようにするのが簡単？

</details><!--}}}-->


<a name = "Ai__mk_binding_depgraph_for_terms"></a>
Ai.mk_binding_depgraph_for_terms
--------------------------------

```ocaml
let mk_binding_depgraph_for_terms id vars =
  if vars = [] then
     ^^^^^^^^^
    register_dep_binding_env id [[]]
  else
    let f = fst (List.hd vars) in
                 ^^^^^^^^^^^^
    let vars' = List.map snd vars in
    let bindings = (!binding_array_nt).(f) in
    let bindings' =
      delete_duplication_unsorted
        (List.rev_map (fun (binding,_)->filter_binding vars' binding) bindings)
```

<details><summary>手を加えることでMoCHiが検証できるようになったコード</summary><!--{{{-->

```ocaml
(* Stub code *)
let rec bot() = bot()
let rand_int() = Random.int 1000
let rand_bool() = Random.bool()
let rec rand_list rand_e () =
  if rand_bool () then
    []
  else rand_e() :: rand_list rand_e ()
let rand_int_list = rand_list rand_int

(* Grammar から型定義を持ってくる *)
type nameNT = int
type nameT = string
type nameV = nameNT * int
type term = NT of nameNT | T of nameT | Var of nameV | App of term * term
type kind = O | Kfun of kind * kind
type nonterminals = (string * kind) array
type varinfo = string array array
type terminals = (nameT * int) list
type rule = (int * term)
type rules = rule array
type gram = {nt: nonterminals; t: terminals; vinfo: varinfo; r: rules; s: nameNT}
(* Automaton からも型定義を持ってくる *)
type state = string
type transfunc = ((state * nameT) * state list) list
type automaton = {alpha: terminals;
                  st: state list;
                  delta: transfunc;
                  init: state
                 }
(* Utilitiesの関数を抽象化 *)
let delete_duplication_unsorted _c =
  rand_list (fun () -> rand_int(), rand_int(), rand_int()) ()

(* その他の使われる関数を抽象化 *)
let rec mk_binding_with_mask _vars _binding: (int * int * int list * int) list =
  rand_list (fun () -> (rand_int(), rand_int(), rand_int_list(), rand_int())) ()
let rec filter_binding (_vars: int list) (_binding : (int * int * int) list) =
  rand_list (fun () -> (rand_int(), rand_int(), rand_int())) ()
let binding_array_nt = ref [||]
let register_dep_binding_env _id _bindings = ()
let ids_in_bindings _bindings = rand_int_list()
let register_dep_penv_binding _id1 _id2 = ()

(*{SPEC}
  external List.hd : (int*int) |len:len>0| list -> (int*int)
{SPEC}*)
let mk_binding_depgraph_for_terms id (vars : (int*int) list) =
  if vars = [] then
    register_dep_binding_env id [[]]
  else
    let f = fst(List.hd vars) in
    let vars' = List.map snd vars in
    let bindings = (!binding_array_nt).(f) in
    let bindings' =
      delete_duplication_unsorted
        (List.rev_map (fun (binding,_)->filter_binding vars' binding) bindings)
    in
    let bindings_with_mask =
      List.rev_map (mk_binding_with_mask vars') bindings'
    in
    let ids = ids_in_bindings bindings' in
    register_dep_binding_env id bindings_with_mask;
    List.iter (fun id1 -> register_dep_penv_binding id1 id) ids
```

+ 手を加えた部分
    + grammar.mlなどから型定義をコピー
    + module importを削除
    + 使われない関数を削除
        + 使われない関数が`Utilities.foo`などを使用しているとOCamlの型検査が通らない（消してしまったので）
        + 上記3つはmliを読み込めば自動化できる
    + `mk_binding_depgraph_for_terms`以外の残った関数を抽象化
        + しないとやはり終わらなかった
    + MoCHiが`(int * int) list`型の比較をsupportしていなかったので
      nilとの比較だけを（雑に）実装してごまかした
+ 自動検証のために必要なこと
    + mliを読み込んで，
        + 型定義をコピー
        + 抽象化された関数を生成
    + `mk_binding_with_mask`のような関数を_適宜_抽象化
        + 抽象化したせいで検証に通らなくなることもあるので判断が難しい？
        + 抽象化しないと通らないこともある
            + （興味の対象外の）assertion failureを起こす
            + 複雑過ぎて計算時間，スペースで死ぬ
    + list equality

```
MoCHi: Model Checker for Higher-Order Problems
  Build: _0b458da (after 2018-12-14 14:31:27 +0900)
  Z3 library version: 4.7.1.0
  HorSat2 version: 0.94
  HoIce version: 1.7.1
  OCaml version: 4.03.0
  Command: mochi-develop mk_binding.ml -bool-init-empty

Safe!

CEGAR-cycles: 4
total: 135.369 sec
  abst: 131.588 sec
  mc: 1.674 sec
  refine: 1.328 sec
```

</details><!--}}}-->


Int Non-Negative
================

<a name = "Stype__arity2sty"></a>
Stype.arity2sty
---------------

```ocaml
let rec arity2sty n =
  if n<0 then assert false
  else if n=0 then STbase
  else STfun(STbase, arity2sty (n-1))

(* 唯一のcaller *)
let alpha2cste alpha =
  List.map (fun (a,k) ->
    if k<0 then (a, new_tvar()) else (a, arity2sty k)) alpha
```

+ 直前で`k<0`かどうかcheckしているのでsafe

### 手を加えることでMoCHiが検証できるようになったコード

```ocaml
(* from grammar.ml *)
type kind = O | Kfun of kind * kind

type tvar = int
type st = STvar of (st option) ref | STbase | STfun of st * st
let dummy_type = STbase
let new_tvid() = ref None
let new_tvar() = STvar(new_tvid())

let rec arity2sty n =
  if n<0 then assert false
  else if n=0 then STbase
  else STfun(STbase, arity2sty (n-1))

let alpha2cste alpha =
  List.map (fun (a,k) -> if k<0 then (a, new_tvar()) else (a, arity2sty k)) alpha
```

+ 手を加えた部分
    + module importを削除
    + 使わない関数を削除
    + grammar.mlから`kind`の定義をコピー

+ 自動検証のために必要なこと
    + `Ai.mk_binding_depgraph_for_terms`と同様

```
MoCHi: Model Checker for Higher-Order Problems
  Build: _0b458da (after 2018-12-14 14:31:27 +0900)
  Z3 library version: 4.7.1.0
  HorSat2 version: 0.94
  HoIce version: 1.7.1
  OCaml version: 4.03.0
  Command: mochi arity2sty.ml

（中略）

Safe!

CEGAR-cycles: 2
total: 1.269 sec
  abst: 0.547 sec
  mc: 0.013 sec
  refine: 0.506 sec
```

Matching
========

<a name = "Ai__nt_in_term_with_linearity"></a>
Ai.nt_in_term_with_linearity
----------------------------

```ocaml
let rec nt_in_term_with_linearity term =
  match term with
  | Var(_) -> ([], [])
  | T(_) ->  ([], [])
  | NT(f) -> ([f], [])
  | App(_,_) ->
      let (h,terms) = Grammar.decompose_term term in
      match h with
      | NT(f) -> let nts = nt_in_terms terms in
          if List.mem f nts then ([],nts)
          else ([f],nts)
      | Var(_) -> ([], nt_in_terms terms)
      | T(a) ->
          let linearity_info = Hashtbl.find tab_linearity a in
          nt_in_terms_with_linearity terms linearity_info 0 ([],[])
      | _ -> assert false
```

<details><!--{{{-->

```ocaml

```

</details><!--}}}-->

<a name = "Ai__term2head"></a>
Ai.term2head
------------

```ocaml
let rec decompose_term t =
  match t with
  | (NT(_) | T(_) | Var(_)) -> (t, [])
  | App(t1,t2) -> let (h,ts) = decompose_term t1 in (h,ts@[t2])

let term2head h =
  match h with
  | Var(x) -> Hvar(x)
  | NT(f) -> Hnt(f)
  | T(a) -> Ht(a)
  | _ -> assert false

(* caller *)
let rec convert_term t =
  let (h,terms) = Grammar.decompose_term t in
       ^
  if terms=[] then (term2head h, [])
                    ^^^^^^^^^^^
  else
    let aterms = List.map convert_term terms in
    let vars = vars_in_aterms aterms in
    let id =
      try
        Hashtbl.find tab_terms_id aterms
      with Not_found ->
        let id = new_terms_id() in
        Hashtbl.add tab_terms_id aterms id;
        (!tab_id_terms).(id) <- (aterms,terms,vars);
        id
    in
    (term2head h, [id])
     ^^^^^^^^^^^
```

<details><!--{{{-->

```ocaml
type nameNT = int (* names of non-terminal symbols; they are just integers **)
type nameT = string  (* names of terminal symbols **)
type nameV = nameNT * int (* pair of the non-terminal and the variable index *)
type term = NT of nameNT | T of nameT | Var of nameV | App of term * term
type head = Hnt of nameNT | Hvar of nameV | Ht of nameT

let rand_int () = Random.int 100
let rand_bool () = Random.bool ()
let rec rand_list rand_e () =
  if Random.bool () then
    []
  else
    rand_e () :: rand_list rand_e ()
let rand_string() = ""
let rand_nameV (): nameV = (rand_int(), rand_int())

(* 抽象化 *)
let tab_terms_id = Hashtbl.create 100000
let new_terms_id() = rand_int()
let tab_id_terms = ref [||]
let vars_in_aterms : (head * int list) list -> nameV list =
  fun _ -> rand_list (rand_nameV) ()

(* ここから下は元のコードそのまま
 * ただしHashtbl.findがNot_foundを投げ得ることが表現されていない *)

let rec decompose_term t =
  match t with
  | (NT(_) | T(_) | Var(_)) -> (t, [])
  | App(t1,t2) -> let (h,ts) = decompose_term t1 in (h,ts@[t2])

let term2head h =
  match h with
  | Var(x) -> Hvar(x)
  | NT(f) -> Hnt(f)
  | T(a) -> Ht(a)
  | _ -> assert false

(* caller *)
let rec convert_term t =
  let (h,terms) = decompose_term t in
  if terms=[] then (term2head h, [])
  else
    let aterms = List.map convert_term terms in
    let vars = vars_in_aterms aterms in
    let id =
      try
        Hashtbl.find tab_terms_id aterms
      with Not_found ->
        let id = new_terms_id() in
        Hashtbl.add tab_terms_id aterms id;
        (!tab_id_terms).(id) <- (aterms,terms,vars);
        id
    in
    (term2head h, [id])

(*
MoCHi: Model Checker for Higher-Order Problems
  Build: b889e4e (2018-12-17 20:48:51 +0900)
  Z3 library version: 4.7.1.0
  HorSat2 version: 0.94
  HoIce version: 1.7.1
  OCaml version: 4.03.0
  Command: mochi-improve_encode_rec term2head.ml

Safe!

CEGAR-cycles: 3
total: 141.248 sec
  abst: 112.715 sec
  mc: 10.098 sec
  refine: 16.716 sec
*)
```

</details><!--}}}-->


その他
======

Pobdd.make_node
---------------

`pobdd.ml`ではFunctorが使われているので対応する必要がある．
それを除くとcaller `bdd_var`, `bdd_nvar`に対しては`Ai.mk_binding_depgraph_for_terms`と同じ方法でできる

<details>MoCHiに渡せば検証が通るコード<!--{{{-->

```ocaml
type var = int
type id = int

type bdd = Node of var * bdd * bdd * id * var list | Leaf of bool;;
type bdd_key = var * id * id;;
type zdd = bdd

let rand_int () = Random.int 100
let rand_bool () = Random.bool ()
let rec rand_list rand_e () =
  if Random.bool () then
    []
  else
    rand_e () :: rand_list rand_e ()
let rec rand_bdd () =
  if Random.bool () then
    Leaf(Random.bool ())
  else
    Node(rand_int (),
         rand_bdd (),
         rand_bdd (),
         rand_int (),
         rand_list rand_int ())

(* これを module NodeHash = Hashtbl.Make(HashType) から自動生成したい *)
type _NodeHash_t = NodeHash_t
let _NodeHash_create : int -> _NodeHash_t =
  fun _ -> NodeHash_t
let _NodeHash_add : _NodeHash_t -> bdd_key -> bdd -> unit =
  fun _ _ _ -> ()
let _NodeHash_find : _NodeHash_t -> bdd_key -> bdd =
  fun _ _ ->
    if rand_bool()
    then raise Not_found
    else rand_bdd()
let node_hashtbl = _NodeHash_create 1000

(* ここから下は2点を除いて元のコードそのまま *)

let id_seed = ref 2
let gen_id () =
  let i = !id_seed in
  incr id_seed
  i

let bdd_vars = function
  | Leaf _ -> []
  | Node(_,_,_,_,l) -> l;;

let rec merge_vars l1 l2 = if l1 == l2 then l1 else
    match (l1,l2) with
    | ([],l2) -> l2
    | (l1,[]) -> l1
    | (a::l1,b::l2) ->
      let d = compare a b  in (* 1点目: 元はElt.compare *)
      if d < 0 then a::merge_vars l1 (b::l2)
      else if d > 0 then b:: merge_vars (a::l1) l2
      else a :: merge_vars l1 l2;;

let node_id = function
  | Leaf(true) -> 0
  | Leaf(false) -> 1
  | Node(_,_,_,x,_) -> x;;

let make_node (v,t1,t2) =
  let i1 = node_id t1 in
  let i2 = node_id t2 in
  let key = (v,i1,i2) in
  assert (i1 <> i2);
  try
    _NodeHash_find node_hashtbl key (* 2点目 NodeHash.findを_Nodehash_findに置き換え *)
  with Not_found -> begin
      let i = gen_id () in
      let l1 = bdd_vars t1 in
      let l2 = bdd_vars t2 in
      let l = merge_vars l1 l2 in
      let t = Node (v,t1,t2,i,v::l) in
      _NodeHash_add node_hashtbl key t; (* 2点目 NodeHash.addを_Nodehash_addに置き換え *)
      t
    end;;

let bdd_true  = Leaf true;;
let bdd_false = Leaf false;;

let bdd_var v = make_node (v, bdd_true, bdd_false);;

(*
MoCHi: Model Checker for Higher-Order Problems
  Build: _b889e4e (after 2018-12-17 20:48:51 +0900)
  Z3 library version: 4.7.1.0
  HorSat2 version: 0.94
  HoIce version: 1.7.1
  OCaml version: 4.03.0
  Command: mochi node_id2.ml -bool-init-empty

Safe!

CEGAR-cycles: 3
total: 9.892 sec
  abst: 6.827 sec
  mc: 0.091 sec
  refine: 1.642 sec
*)
```

</details><!--}}}-->

