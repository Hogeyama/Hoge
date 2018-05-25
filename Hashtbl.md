
<a name = "register_nt"></a>
### Conversion.register_nt

+ HorSat2への入力次第では`DuplicatedNonterminal`の送出が避けられない

```ocaml
type register_nt
  :  { ntname : string | not (Hashtbl.mem ntname tab_ntname2id) }
  -> unit
let register_nt ntname =
  if Hashtbl.mem tab_ntname2id ntname then raise (DuplicatedNonterminal ntname)
  else
    let nt = new_nt() in
      Hashtbl.add tab_ntname2id ntname nt;
      (!nttab).(nt) <- (ntname,O) (* for the moment, ignore the kind *)
```

<a name = "lookup_ntid"></a>
### Conversion.lookup_ntid

+ HorSat2への入力次第では`UndefinedNonterminal`の送出が避けられない

```ocaml
type lookup_ntid
  :  { ntname : string | Hashtbl.mem ntname tab_ntname2id }
  -> Grammar.nameNT
let lookup_ntid ntname =
  try Hashtbl.find tab_ntname2id ntname
  with Not_found ->
      raise (UndefinedNonterminal ntname)
```

<a name = "evaluate_eterm"></a>
### Cegen.evaluate_eterm

TODO

```ocaml
let rec evaluate_eterm eterm env =
  let (h,termss) = decompose_eterm eterm in
  match h with
  | ENT(f,ity,ntyid) ->
      begin try
        let (vte,body) =
              try
                Hashtbl.find tracetab (f,ity)
              with Not_found -> begin
                register_backchain f ity ntyid; (* これもfailし得る *)
                Hashtbl.find tracetab (f,ity)
              end
        in
        let (vte',body') = rename_vte_eterm vte body in
        let env' = mk_env vte' termss in
        evaluate_eterm body' (env'@env)
      with
        Not_found -> assert false
      end
 | ET(a,aty) ->
      begin try
        let trees = List.map (fun ts -> evaluate_eterms ts env) termss in
          Node(a, trees)
      with
        Not_found -> assert false
      end
 | EVar(v,aty) ->
      begin try
        let eterm1 = List.assoc (v,aty) env in
            evaluate_eterm (compose_eterm eterm1 termss) env
      with
        Not_found -> assert false
      end
 | ECoerce(aty1,aty2,t) ->
      begin try
        begin match (aty1,aty2) with
        | (ItyQ(q1),ItyQ(q2)) -> assert (q1=q2); evaluate_eterm t env
        | (ItyFun(_,ty11,aty11), ItyFun(_,ty21,aty21)) ->
             begin match termss with
             | [] -> assert false
             | ts::termss' ->
                 let tyterms = List.combine ty21 ts in
                 let ts' = List.map
                             begin fun aty ->
                               let (aty',t') = List.find (fun (aty',_)->Type.subtype aty' aty) tyterms in
                               if aty=aty' then t' else ECoerce(aty',aty,t')
                             end
                             ty11
                 in
                 let t1 = if aty11=aty21 then EApp(t,ts') else
                          ECoerce(aty11,aty21,EApp(t,ts'))
                 in evaluate_eterm (compose_eterm t1 termss') env
             end
        | _ -> assert false
        end
      with
        Not_found -> assert false
      end
  | _ -> assert false
and evaluate_eterms ts env =
  match ts with
    [] -> Bottom
  | t::ts' ->
     let t1 = evaluate_eterm t env in
     let t2 = evaluate_eterms ts' env in
        merge_tree t1 t2
```
