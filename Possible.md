
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

使われていない関数，moduleを削除すれば検証できる


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

(* 'Grammar' から型定義を持ってくる *)
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
(* 'Automaton' からも型定義を持ってくる *)
type state = string
type transfunc = ((state * nameT) * state list) list
type automaton = {alpha: terminals;
                  st: state list;
                  delta: transfunc;
                  init: state
                 }
(* 'Utilities'の関数を抽象化 *)
let delete_duplication_unsorted _c =
  rand_list (fun _ -> rand_int(), rand_int(), rand_int()) ()

(* その他の使われる関数を抽象化 *)
let rec split_vars _vars _j = (rand_int_list(), rand_int_list())
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
    + `mk_binding_depgraph_for_terms`以外の残った関数を抽象化
        + しないとやはり終わらなかった
        + 全部抽象化する必要はなかった気はする
+ 自動検証のために必要なこと
    + 型定義のコピーを自動化（mliだけは渡すようにする？）
    + 使わない関数・moduleをOCamlの型検査が通るように適当に生成する
    + （今回はしなくてもよかったが）使われる関数も適当に抽象化する

#### TODO

+ 関数を抽象化すると検証できなくなる場合と抽象化しないと検証できない場合とがある

    + 抽象化すると検証できない: その関数で保証されるinvariantがある
    + 抽象化しないとと検証できない: その関数自身が失敗する，関数が複雑過ぎて計算量で死ぬ

  どう選択するべき？

    + 「最初は全て抽象化して，検証に失敗したら具体化していく」という方針を取るとして，
      どの関数を

+ listのequalityのちょろまかしてある

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

(* 唯一のcaller *)
let alpha2cste alpha =
  List.map (fun (a,k) ->
    if k<0 then (a, new_tvar()) else (a, arity2sty k)) alpha
```

+ 手を加えた部分
    + module importを削除
    + 使わない関数を削除
    + grammar.mlから`kind`の定義をコピー
+ 自動検証のために必要なこと
    + `grammar.ml(i)`から型定義を持ってくる
    + 使わない関数・moduleをOCamlの型検査が通るように適当に生成する
    + （今回はしなくてもよかったが）使われる関数も適当に抽象化する


Matching
========

<a name = "Cegen__mk_ehead"></a>
Cegen.mk_ehead
--------------

```ocaml
let mk_ehead h aty =
  match h with
  | NT(_) -> assert false
  | T(a) -> ET(a,aty)
  | Var(x) -> EVar(x,aty)
  | App(_,_) -> assert false

(* caller *)
and find_headtype ntyid vte h aty k =
  match h with
  | NT(f) ->
      let ty = ty_of_ntall_q f (Type.codom_of_ity aty) in
      let ty' = List.filter
          (fun (aty1,ntyid') ->
             ntyid'<ntyid && rangesubtype aty1 aty k) ty in
      List.map (fun (aty1,i) -> (ENT(f,aty1,i), aty1)) ty'
  | _ ->
      let ty = lookup_headty vte h aty in
      let ty' = List.filter
          (fun aty1 -> rangesubtype aty1 aty k) ty in
      List.map (fun aty1 -> (mk_ehead h aty1, aty1)) ty'
                             ^^^^^^^^^^^^^^^

(* caller of find_headtype *)
let rec find_derivation ntyid vte term aty =
  let (h,terms) = Grammar.decompose_term term in
       ^
  let k = List.length terms in
  let head_typings = find_headtype ntyid vte h aty k in
                     ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
  try
    List.iter (fun (eh,aty0) ->
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

+ `NT(_) -> assert false`の方は`find_headtype`内のmatchを見ればunreachableだと分かる
+ `App(_,_) -> assert false`の方は`find_derivation`の方で`decompose_term`を呼んでいる所を見ればunreachableだと分かる
+ 問題点
    + term`h`が関数`h'`にエンコードされる
    + matchの度に`h' []`が評価されるので`NT`にmatchしないはずのものがmatchすることになる
        + 非決定性を含む関数で近似する場合
+ 解決策
    + `h' []`の情報だけは別に持つ
        + ややad-hocだが実用上は十分か（二重にmatchさせる場合は同じ問題が起こる）
    + 11/27 佐藤先生が実装してくださいました [commit](https://bitbucket.org/ryosu_sato/mochi/commits/49fed12cdf44b155a3dfcda2f09b4a62085a5326)

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

+ `decompose_term`の返り値は`App(_,_)`にmatchしないのでsafe


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


<a name = "Saturate__ty_of_head"></a>
Saturate.ty_of_head
-------------------

```ocaml
let ty_of_head h venv =
  match h with
  | NT(f) -> (ty_of_nt f)
  | T(a) -> (ty_of_t a)
  | Var(v) -> ty_of_var venv v
  | _ -> assert false
(* caller *)
let ty_of_term2 venv term =
  let (h,terms) = Grammar.decompose_term term in
       ^
  let ty = ty_of_head h venv in
           ^^^^^^^^^^^^
  let arity = List.length terms in
  let tys_ity_list = List.map (split_ity arity) ty in
  check_args tys_ity_list terms venv []
```


<a name = "Saturate__ty_of_head_q"></a>
Saturate.ty_of_head_q
---------------------

```ocaml
let ty_of_head_q h venv q =
  match h with
  | NT(f) -> List.map (fun ity -> (ity,[])) (ty_of_nt_q f q)
  | T(a) -> List.map (fun ity -> ity,[]) (ty_of_t_q a q)
  | Var(v) -> let ty = ty_of_var venv v in List.map (fun ity->(ity,[(v,[ity])])) ty
  | _ -> assert false
(* caller *)
let match_head_types h venv arity ity =
  match ity with
  | ItyQ(q) -> ...
  | _ ->
      let ty = List.filter (fun (ity1,_) ->
          subtype (get_range ity1 arity) ity) (ty_of_head_q h venv (codom_of_ity ity)) in
                                               ^^^^^^^^^^^^
      List.map (fun (ity,vte) -> (get_argtys arity ity, vte)) ty
(* match_head_typesの唯一のcaller *)
let rec check_ty_of_term venv term ity =
  match term with
  | App(_,_) ->
      let (h,terms) = Grammar.decompose_term term in
      let tyss = match_head_types h venv (List.length terms) ity in
                 ^^^^^^^^^^^^^^^^^^
      let vte = check_argtypes venv terms tyss in vte
  ...
```

<a name = "Saturate__ty_of_head_q2"></a>
Saturate.ty_of_head_q2
---------------------

`ty_of_head_q2`とほぼ同じ


<a name = "Cegen__lookup_headty"></a>
Cegen.lookup_headty
-------------------

```ocaml
let lookup_headty vte h aty =
  match h with
  | T(a) ->
      let q = Type.codom_of_ity aty in
      Type.ty_of_t_q a q
  | Var(x) ->
      (try List.assoc x vte with Not_found -> assert false) (* ここは別問題 *)
  | NT(_) | App(_,_) -> assert false
                        ^^^^^^^^^^^^

(* 唯一のcaller *)
and find_headtype ntyid vte h aty k =
  match h with
  | NT(f) ->
      let ty = ty_of_ntall_q f (Type.codom_of_ity aty) in
      let ty' = List.filter
          (fun (aty1,ntyid') ->
             ntyid'<ntyid && rangesubtype aty1 aty k) ty in
      List.map (fun (aty1,i) -> (ENT(f,aty1,i), aty1)) ty'
  | _ ->
      let ty = lookup_headty vte h aty in
               ^^^^^^^^^^^^^^^^^^^^^^^
      let ty' = List.filter
          (fun aty1 -> rangesubtype aty1 aty k) ty in
      List.map (fun aty1 -> (mk_ehead h aty1, aty1)) ty'

(* find_headtypeの唯一のcaller *)
let rec find_derivation ntyid vte term aty =
  let (h,terms) = Grammar.decompose_term term in
       ^
  let k = List.length terms in
  let head_typings = find_headtype ntyid vte h aty k in
                     ^^^^^^^^^^^^^
  try
    List.iter (fun (eh,aty0) ->
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

その他
======

Pobdd.make_node
---------------

caller `bdd_var`, `bdd_nvar`に対しては検証できる．[詳細](./TrivialProblem.md#Pobdd__make_node)

