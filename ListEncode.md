
List.assoc, List.find, List.sorted
==================================

`List.assoc`，`List.find`，`List.sorted`


+ `Ai.add_binding_st`

  + arrayとList.assoc

    <details><summary>code</summary><!--{{{-->

    ```ocaml
    let add_binding_st f rho qs =
      let rho' = add_index rho 0 in
      let qref = try List.assoc rho' (!binding_array_nt).(f) with Not_found -> assert false in
      qref := merge_and_unify compare qs !qref
    ```

    </details><!--}}}-->

+ `Saturate.pick_vte`

  + `List.find`

    <details><summary>code</summary><!--{{{-->

    ```ocaml
    let pick_vte ity ity_vte_list =
      try
        snd(List.find (fun (ity',_vte)-> subtype ity' ity) ity_vte_list )
      with Not_found -> raise Untypable
    ```

    </details><!--}}}-->

+ `Saturate.check_ty_of_term`

  + List.find, List.assoc

    <details><summary>code</summary><!--{{{-->

    ```ocaml
    let rec check_ty_of_term venv term ity =
      match term with
      | App(_,_) ->
          let (h,terms) = Grammar.decompose_term term in
          let tyss = match_head_types h venv (List.length terms) ity in
          let vte = check_argtypes venv terms tyss in vte
      | Var(v) ->
          begin try
            let ity1 = List.find (fun ity1 -> subtype ity1 ity) (ty_of_var venv v) in
                       ^^^^^^^^^
            [(v, [ity1])]
          with
            Not_found -> raise Untypable
          end
      | T(a) ->
          let q = codom_of_ity ity in
          if List.exists (fun ity1 -> subtype ity1 ity) (ty_of_t_q a q)
             ^^^^^^^^^^^
          then []
          else raise Untypable
      | NT(f) ->
          let q = codom_of_ity ity in
          if List.exists (fun ity1 -> subtype ity1 ity) (ty_of_nt_q f q)
             ^^^^^^^^^^^
          then []
          else raise Untypable
    ```

    </details><!--}}}-->

+ `Scc.split_list_at`
  + `List.mem`が必要

+ `Saturate.ty_of_var`
  + 実質`List.exist`

後回し

+ `Grammar`.ml|218 col 5| `assert false (* raise (UndefinedNonterminal (name_of_nt x)) *)`
  List.assoc 無理
+ `Grammar.`|223 col 11| | [] -> assert false
  `List.find (List.mem _) _` 無理

saturate.ml|901 col 10| else raise Untypable
  List.exists
saturate.ml|901 col 10| else raise Untypable
  List.find
saturate.ml|901 col 10| else raise Untypable
  List.exists
saturate.ml|906 col 10| else raise Untypable
  List.exists
saturate.ml|911 col 11| [] -> raise Untypable
  これは行けるかな？いや再帰の部分で無理だ
  merge_two_vtes vte0 (check_argtypes_aux venv terms tys)でUntypableを投げないものが存在する
pobdd.ml|329 col 7| assert (sorted (List.map (function POS v | NEG v -> v) vl));
  無

上のUntypableもcatchされたりされなかったりしそう
以下catchされるかもしれない

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
理
