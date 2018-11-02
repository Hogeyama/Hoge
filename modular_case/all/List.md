
hd
===============================================================================

+ `Ai.mk_binding_depgraph_for_terms`

    + 直前でvarsがnilでないことを確認しているので行ける → [詳細](../can_be_verified.md#Ai__mk_binding_depgraph_for_terms)

+ `AlternatingAutomaton.from_transitions`

    + 追い切れない

+ `Cegen.find_ce`
    + `let (_,ntyid) = List.hd ((!nteallref).(0).(0)) in`
    + 見るからに無理

+ `Conversion.convert`

    + `let q0 = fst (fst (List.hd transitions)) in`
    + parse結果の`transition`がnilでないことを言う必要がある．難しい

+ `Grammar.register_recfun` :`let singletons = List.map List.hd (List.filter list_singleton scc)`

    + 検証できそう
    + だが使われていない関数

+ `Main.report_breakdown`:
    + `let last = if !times=[] then start_t else List.hd !times in`
    + 検証できそう → [詳細](../can_be_verified.md#Main__report_breakdown)

+ `Saturate.register_terms_te`

    + 行けるかも → TODO
    + `let tys = List.hd (tyseq2tyss !tyseqref 0) in`
    + `tyseq2tyss`がnilを返さないことを言えば良いが，頑張れば言えそう

+ `Utilities.list_max`

    + callerは`Stype.order_of_nste`:

        ```
        let order_of_nste nste =
          let nste' = indexlist (Array.to_list nste) in
          let ordmap = List.map (fun (nt, sty) -> (nt, order_of_sty sty)) nste' in
          let x = list_max (fun (_nt1,ord1) ->fun (_nt2,ord2) -> compare ord1 ord2) ordmap in
          x
        ```

        + これのcallerは`Stype.tcheck`:

            ```
            let tcheck g alpha =
              let cste = alpha2cste alpha in
              let num_of_nts = Array.length g.nt in
              let nste = Array.make num_of_nts dummy_type in ...
            ```

          `Array.length g.nt > 0`を言う必要がある．厳しいか

tl
==

なし

combine
=======

+ `Ai.mk_trtab`

    ```
    let arity = List.length qs in
    let x = Array.make arity [] in
    let indices = fromto 0 arity in
    List.iter
      (fun (i,q') -> x.(i) <- [state2id q'])
      (List.combine indices qs);
    ```

    + 検証できそう → [詳細](../can_be_verified.md#Ai__mk_trtab)

+ `Cegen.mk_env`:
    + 難しいやつ
    + callerは`Cegen.evaluate_eterm`:

        ```
        let rec evaluate_eterm eterm env =
          let (h,termss) = decompose_eterm eterm in
          match h with
          | ENT(f,ity,ntyid) ->
            (try
               let (vte,body) =
                 try Hashtbl.find tracetab (f,ity) with Not_found ->
                   (register_backchain f ity ntyid;
                    Hashtbl.find tracetab (f,ity)) in
               let (vte',body') = rename_vte_eterm vte body in
               let env' = mk_env vte' termss in
               ...
        ```

      `Hashtbl`も絡んでいるので難しい

+ `Cegen.merge_trees`

    + 木をmergeする．難しい

+ `cegen.evaluate_eterm`

    + 全然わからん

      ```
      let rec evaluate_eterm eterm env =
        let (h,termss) = decompose_eterm eterm in
        match h with
        ...
        | ECoerce(aty1,aty2,t) ->
            try
              (match (aty1,aty2) with
               | (ItyQ(q1),ItyQ(q2)) -> assert (q1=q2); evaluate_eterm t env
               | (ItyFun(_,ty11,aty11), ItyFun(_,ty21,aty21)) ->
                 (match termss with
                  | [] -> assert false
                  | ts::termss' ->
                      let tyterms = List.combine ty21 ts in
            ...
        ...
      ```

+ `Conversion.normalize_term`

    + 検証できそう → TODO
    + callerを見なくてよい

      ```
        let arity = List.length vars in
        let nt = new_ntaux() in
        let subst = List.combine vars (List.map (fun i->Var(nt,i)) (fromto 0 arity)) in
      ```

+ `utilities.indexlist`, `indexlistl`

    ```
    let indexlist l =
      let len = List.length l in
      let indices = fromto 0 len in
      List.combine indices l

    let indexlistr l =
      let len = List.length l in
      let indices = fromto 0 len in
      List.combine l indices
    ```


assoc
=====

30個（とりあえず列挙するだけ）

ai.ml|124 col 19| let arity = List.assoc a m.AlternatingAutomaton.alpha in
ai.ml|378 col 18| let qref = try List.assoc rho' (!binding_array_nt).(f) with Not_found -> assert false in
alternatingAutomaton.ml|18 col 15| let cls = List.assoc v delta in
alternatingAutomaton.ml|30 col 15| let fml = List.assoc v delta in
automaton.ml|14 col 3| List.assoc (q,a) m.delta
cegen.ml|90 col 20| | Var(x) -> (try List.assoc x vte with Not_found -> assert false)
cegen.ml|237 col 30| | EVar(v,ity) -> (try EVar(List.assoc v vmap, ity) with Not_found -> eterm)
cegen.ml|285 col 21| let eterm1 = List.assoc (v,aty) env in
conversion.ml|49 col 36| Syntax.Name(s) -> (try Var(List.assoc s vmap) with Not_found -> T(s))
grammar.ml|132 col 20| let arity_of_t a = List.assoc a (!gram).t
grammar.ml|162 col 9| List.assoc x s
grammar.ml|171 col 9| List.assoc x s
grammar.ml|216 col 5| List.assoc x dmap
saturate.ml|95 col 3| List.assoc a m.alpha
saturate.ml|131 col 21| let fml = List.assoc (q,a) m.AlternatingAutomaton.delta in
scc.ml|8 col 28| let get_node (g:graph) x = List.assoc x g;;
scc.ml|52 col 31| let (_,_,nextr) = List.assoc x g in
scc.ml|57 col 20| try (let _ = List.assoc y g' in g') with
scc.ml|154 col 29| let (nextr,_) = List.assoc x g in
scc.ml|159 col 20| try (let _ = List.assoc y g' in g') with
scc.ml|163 col 25| let (nextr, cacher) = List.assoc n g in
stype.ml|55 col 21| STvar v -> (try List.assoc v sub with Not_found -> st)
stype.ml|149 col 29| let lookup_stype_t a cste = List.assoc a cste
typing.ml|207 col 37| (try List.filter (eqrty n rty) (List.assoc a cte)
typing.ml|210 col 38| ( try List.filter (eqrty n rty) (List.assoc v vte)
typing.ml|288 col 27| let to_be_checked = List.assoc f dmap in
typing.ml|301 col 27| let to_be_checked = List.assoc f dmap in
utilities.ml|235 col 5| List.assoc var s
utilities.ml|246 col 18| let env_lookup = List.assoc
utilities.ml|321 col 9| (* like List.assoc, but with a specialized equality function *)

