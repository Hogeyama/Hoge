
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
                                         ^^^^^^^^^^^
```

+ 直前で`k<0`かどうかcheckしているのでsafe


Nonempty List
=============

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
  let k = List.length terms in
  let head_typings = find_headtype ntyid vte h aty k in
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

+ `mk_ehead`と同じようにできるはず


