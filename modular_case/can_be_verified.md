
List.hd
=======

<a name = "Ai__mk_binding_depgraph_for_terms"></a>
Ai.mk_binding_depgraph_for_terms
--------------------------------

```ocaml
let mk_binding_depgraph_for_terms id vars =
  if vars = [] then
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

直前でnilでないことをcheckしているのでsafe

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

[indexlist](./OK.md#Utilities__inexlist)と同様

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

[indexlist](./OK.md#Utilities__inexlist)と同様

assert false
============

<a name = "Ai__merge_statevecs"></a>
Ai.merge_statevecs
------------------

```ocaml
let rec merge_statevecs qsvecs =
  match qsvecs with
  | [] -> assert false
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
                 ^^^^^^^^^^^^^^^^^^^^^^^^^^^ (* こっちは厳しい *)
      ...
(* caller *)
let rec expand() =
  match dequeue_node() with
  | None -> print_string ("size of ACG: "^(string_of_int (ATermHashtbl.length nodetab))^"\n")
  | Some(aterm,qs) -> process_node(aterm,qs); expand()
                      ^^^^^^^^^^^^^^^^^^^^^^
```

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

`decompose_term`のパターン

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
      (try List.assoc x vte with Not_found -> assert false)
                                              ^^^^^^^^^^^^
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
```

+ `Var(x) -> ...`の方はList.assocなのでできない
+ `_ -> ...`の方は`mk_ehead`と同じようにできるはず


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

`decompose_term`のパターン


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
(* caller of match_head_types *)
let rec check_ty_of_term venv term ity =
  match term with
  | App(_,_) ->
      let (h,terms) = Grammar.decompose_term term in
      let tyss = match_head_types h venv (List.length terms) ity in
                 ^^^^^^^^^^^^^^^^^^
      let vte = check_argtypes venv terms tyss in vte
  ...
```

`decompose_term`のパターン

<a name = "Saturate__ty_of_head_q2"></a>
Saturate.ty_of_head_q2
---------------------

`ty_of_head_q2`と同じようなパターン


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

