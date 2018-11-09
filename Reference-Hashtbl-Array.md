
Reference, Array, Hashtbl
=========================

Reference
---------

+ `Ai.expand_varheadnode`

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

+ `Setqueue.dequeue`

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

+ `Cegen.find_ce`
  + `let (_,ntyid) = List.hd ((!nteallref).(0).(0)) in`

+ `Cegen.find_ce`
  + `let (_,ntyid) = List.hd ((!nteallref).(0).(0)) in`

+ `type tyseq = TySeq of (Grammar.ty * (tyseq ref)) list | TySeqNil`に関するエラー
  + `Saturate.tyseq_mem`
  + `Saturate.tyseq_subsumed`
  + `Saturate.tyseq_add_wo_subtyping`
  + `Saturate.tyseq_rem_subtyping_aux`
  + `Saturate.tyseq_merge_tys`

Array
-----

+ `Ai.add_binding_st`
  + `try List.assoc rho' (!binding_array_nt).(f) with Not_found -> assert false in`

    ```ocaml
    let rec ty_of_var venv (f,i) =
      match venv with
      | [] -> assert false
      | (j1,j2,tys)::venv' ->
          if j1<=i && i<=j2 then
            proj_tys f (i-j1) tys
          else ty_of_var venv' (f,i)
    ```

+ `Cegen.find_ce`
  + `let (_,ntyid) = List.hd ((!nteallref).(0).(0)) in`

+ `Saturate.register_terms_te`
  + `let tys = List.hd (tyseq2tyss !tyseqref 0) in`

+ `Utilities.list_max`
  + `f c (List.tl l) (List.hd l)`
  + caller

    ```
    let order_of_nste nste =
      let nste' = indexlist (Array.to_list nste) in
      let ordmap = List.map (fun (nt, sty) -> (nt, order_of_sty sty)) nste' in
      let x = list_max (fun (_nt1,ord1) ->fun (_nt2,ord2) -> compare ord1 ord2) ordmap in
      x
    ```

Hashtbl
-------

+ `Ai.id2state`
+ `Ai.state2id`
+ `Ai.register_newnode`
+ `Type.lookup_cte`

<a name = "cegenevaluate_eterm"></a>
+ `Cegn.evaluate_eterm`
    + `mk_env vte' termss`を呼ぶときに`vte'`と`termss`の長さが同じである必要がある
+ `Cegen.evaluate_eterm`

