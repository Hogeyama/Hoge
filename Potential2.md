
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

+ 問題
    + `Ai.mk_binding_depgraph_for_terms`と同じ方法でやろうとすると検証が終わらない．`-bool-init-empty`を付けても同様
    + `eterm`の型が複雑なのが原因？

<details>MoCHiに渡したコード<!--{{{-->

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
and nt_in_terms_with_linearity terms linearity_info i (nts1,nts2) =
  match terms with
    [] -> (nts1,nts2)
  | t::terms' ->
      let (nts1',nts2') =
        if linearity_info.(i) then
          nt_in_term_with_linearity t
        else ([], Grammar.nt_in_term t)
      in
      let (nts1'',nts2'') = merge_nts_lin (nts1',nts2') (nts1,nts2) in
      nt_in_terms_with_linearity terms' linearity_info (i+1) (nts1'',nts2'')
```

相互再帰呼び出しのせいでうまく行かない？

<details><summary>試したコード</summary><!--{{{-->

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
let nt_in_terms terms = rand_list rand_int ()
let _Grammar_nt_in_term _ = rand_list rand_int ()
let tab_linearity: (string, bool array) Hashtbl.t = Hashtbl.create 100
let merge_nts_lin : int list * int list -> int list * int list -> int list * int list =
  fun _ _ -> (rand_list rand_int (), rand_list rand_int ())

(***********************************************************************************)

let rec decompose_term t =
  match t with
  | (NT(_) | T(_) | Var(_)) -> (t, [])
  | App(t1,t2) -> let (h,ts) = decompose_term t1 in (h,ts@[t2])

let rec nt_in_term_with_linearity term =
  match term with
  | Var(_) -> ([], [])
  | T(_) ->  ([], [])
  | NT(f) -> ([f], [])
  | App(_,_) ->
      let (h,terms) = decompose_term term in
      match h with
      | NT(f) -> rand_list rand_int (), rand_list rand_int ()
          (* let nts = nt_in_terms terms in *)
          (*   if List.mem f nts then ([],nts) *)
          (*   else ([f],nts) *)
      | Var(_) -> ([], nt_in_terms terms)
      | T(a) ->
          let linearity_info = Hashtbl.find tab_linearity a in
          nt_in_terms_with_linearity terms linearity_info 0 ([],[])
      | _ -> assert false

and nt_in_terms_with_linearity terms linearity_info i (nts1,nts2) =
  match terms with
    [] -> (nts1,nts2)
  | t::terms' ->
      (* let (nts1',nts2') = *)
      (*   if linearity_info.(i) then *)
      (*     nt_in_term_with_linearity t *)
      (*   else ([], _Grammar_nt_in_term t) *)
      (* in *)
      (* let (nts1'',nts2'') = merge_nts_lin (nts1',nts2') (nts1,nts2) in *)
      let (nts1'',nts2'') = rand_list rand_int (), rand_list rand_int() in
      nt_in_terms_with_linearity terms' linearity_info (i+1) (nts1'',nts2'')

let main = nt_in_term_with_linearity
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
  ...
```

TODO

<a name = "Saturate__ty_of_head_q2"></a>
Saturate.ty_of_head_q2
---------------------

`ty_of_head_q2`とほぼ同じ

TODO

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

TODO

List.combine
============

<a name = "Utilities__inexlist"></a>

Utilities.indexlist
-------------------

```ocaml
let rec fromto m n =
  if m>=n then [] else m::(fromto (m+1) n);;

let indexlist l =
  let len = List.length l in
  let indices = fromto 0 len in
  List.combine indices l

let indexlistr l =
  let len = List.length l in
  let indices = fromto 0 len in
  List.combine l indices
```

述語発見がうまく行かない(`fromto`の問題)

<details><summary></summary><!--{{{-->

```ocaml
let rec fromto m n =
  if m>=n then [] else m::(fromto (m+1) n);;

(*{SPEC}
  external List.combine : xs: int list -> int |len:len=List.length xs| list -> (int*int) list
{SPEC}*)
let indexlist (l : int list) =
  let len = List.length l in
  let indices = zero_to len in
  List.combine indices l
```

`fromto 0`を次の`make_list`にすると通る:

```ocaml
let rec make_list n =
  if n <= 0 then [] else n :: make_list (n-1)
```

</details><!--}}}-->


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

