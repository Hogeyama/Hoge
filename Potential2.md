
自動化できそうな変換によって検証できる形に落とし込めるように見えたけどうまく行ってないケース

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

<details><summary>解決済みの問題点</summary> <!--{{{-->

+ 問題点
    + term`h`が関数`h'`にエンコードされる
    + matchの度に`h' []`が評価されるので`NT`にmatchしないはずのものがmatchすることになる
        + 非決定性を含む関数で近似する場合
+ 解決策
    + `h' []`の情報だけは別に持つ
        + ややad-hocだが実用上は十分か（二重にmatchさせる場合は同じ問題が起こる）
        + 11/27 佐藤先生が実装してくださいました [commit](https://bitbucket.org/ryosu_sato/mochi/commits/49fed12cdf44b155a3dfcda2f09b4a62085a5326)

</details><!--}}}-->

<details><summary>検証</summary><!--{{{-->

`Ai.mk_binding_depgraph_for_terms`と同じ方法でやろうとすると検証が終わらない．
`-bool-init-empty`を付けても同様

```ocaml
(* 手動import *)
type nameNT = int (* names of non-terminal symbols; they are just integers **)
type nameT = string  (* names of terminal symbols **)
type nameV = nameNT * int (* pair of the non-terminal and the variable index *)
type term = NT of nameNT | T of nameT | Var of nameV | App of term * term
type kind = O | Kfun of kind * kind
type state_id = int
type ity_id = int
type ity = ItyQ of state_id | ItyFun of ity_id * ty * ity
and ty = ity list

type eterm = ET of nameT * ity | ENT of nameNT * ity * int
           | EVar of nameV * ity | EApp of eterm * eterm list
           | ECoerce of ity * ity * eterm

(* Stub code *)
let rec bot() = bot()
let rand_int() = Random.int 1000
let rand_bool() = Random.bool()
let rec rand_list rand_e () =
  if rand_bool () then
    []
  else rand_e() :: rand_list rand_e ()
let rand_int_list = rand_list rand_int

let rec rand_ity() = if rand_bool()
  then ItyQ(rand_int())
  else ItyFun(rand_int(), rand_ty(), rand_ity())
and rand_ty() = rand_list rand_ity ()

let rec rand_term () =
  if rand_bool() then
    NT(rand_int())
  else if rand_bool() then
    T("") (* rand_string *)
  else if rand_bool() then
    Var(rand_int(), rand_int())
  else 
    App(rand_term(), rand_term())

(* 抽象化 *)
let ty_of_ntall_q : ity_id -> ity_id -> (ity * ity_id) list =
  fun _ _ -> rand_list (fun () -> (rand_ity(), rand_int())) ()

let codom_of_ity : ity -> state_id =
  fun _ -> rand_int()

let rangesubtype : ity -> ity -> ity_id -> bool =
  fun _ _ _ -> rand_bool()

let lookup_headty : (nameV * ty) list -> term -> ity -> ty =
  fun _ _ _ -> rand_ty()

(* 本体 *)
let rec decompose_term t =
  match t with
    (NT(_)|T(_)|Var(_)) -> (t, [])
  | App(t1,t2) ->
    let (h,ts)=decompose_term t1 in (h,ts@[t2])

let mk_ehead h aty =
  match h with
  | NT(_) -> assert false
  | T(a) -> ET(a,aty)
  | Var(x) -> EVar(x,aty)
  | App(_,_) -> assert false

(* caller *)
let find_headtype ntyid vte h aty k =
  match h with
  | NT(f) ->
      bot()
      (* let ty = ty_of_ntall_q f (codom_of_ity aty) in *)
      (* let ty' = List.filter *)
      (*     (fun (aty1,ntyid') -> *)
      (*        ntyid'<ntyid && rangesubtype aty1 aty k) ty in *)
      (* List.map (fun (aty1,i) -> (ENT(f,aty1,i), aty1)) ty' *)
  | _ ->
      let ty = lookup_headty vte h aty in
      let ty' = List.filter
          (fun aty1 -> rangesubtype aty1 aty k) ty in
      List.map (fun aty1 -> (mk_ehead h aty1, aty1)) ty'

(* caller of find_headtype *)
let rec find_derivation ntyid vte term aty =
  let (h,terms) = decompose_term term in
  let k = List.length terms in
  let _head_typings = find_headtype ntyid vte h aty k in
  bot()

let main ntyid vte aty =
  let term = rand_term() in
  find_derivation ntyid vte term aty
```

次くらいまで単純化するとできる．

```ocaml
type term = Var of int
          | NT of string
          | App of term * term

let rec rand_term () =
  if Random.bool() then
    Var(Random.int 100)
  else if Random.bool() then
    NT("")
  else
    App(rand_term(), rand_term())

let rec decompose_term t =
  match t with
  | Var _ -> (t, [])
  | NT _ -> (t, [])
  | App(t1,t2) -> let (h,ts)=decompose_term t1 in (h,ts@[t2])

let f t (x: int) = match t with
  | Var _ -> x
  | NT _ -> assert false
  | App _ -> assert false

let main xs =
  let (h, ts) = decompose_term (rand_term()) in
  match h with
  | NT _ -> []
  | _ -> List.map (f h) xs

(*
MoCHi: Model Checker for Higher-Order Problems
  Build: _b889e4e (after 2018-12-17 20:48:51 +0900)
  Z3 library version: 4.7.1.0
  HorSat2 version: 0.94
  HoIce version: 1.7.1
  OCaml version: 4.03.0
  Command: mochi decompose_term_simple.ml

Safe!

CEGAR-cycles: 1
total: 36.785 sec
  abst: 20.641 sec
  mc: 15.432 sec
  refine: 0.000 sec
*)
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

