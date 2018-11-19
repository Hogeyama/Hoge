
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

+ `Grammar.find_dep`
  + `List.assoc`
+ `Grammar.find_sc`
  `List.find (List.mem _) _`


他
+ `List.exists`
+ `List.sorted` 1
+ `List.assoc` 9

<!--

pobdd.ml|329 col 7| assert (sorted (List.map (function POS v | NEG v -> v) vl));
  無理
ai.ml|124 col 19| let arity = List.assoc a m.AlternatingAutomaton.alpha in
  されない
ai.ml|378 col 18| let qref = try List.assoc rho' (!binding_array_nt).(f) with Not_found -> assert false in
  されない
cegen.ml|90 col 20| | Var(x) -> (try List.assoc x vte with Not_found -> assert false)
  されない
cegen.ml|285 col 21| let eterm1 = List.assoc (v,aty) env in
  されない
grammar.ml|216 col 5| List.assoc x dmap
  されない
saturate.ml|95 col 3| List.assoc a m.alpha
  されない
saturate.ml|131 col 21| let fml = List.assoc (q,a) m.AlternatingAutomaton.delta in
  されない
grammar.ml|132 col 20| let arity_of_t a = List.assoc a (!gram).t
  されない
scc.ml|8 col 28| let get_node (g:graph) x = List.assoc x g;;
  されない

以下catchされる関数

Saturate.check_ty_of_term
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
  Untypableはcatchされる (`update_ty_of_nt_inc_for_nt_sub_venv`)


alternatingAutomaton.ml|18 col 15| let cls = List.assoc v delta in
  される
alternatingAutomaton.ml|30 col 15| let fml = List.assoc v delta in
  される
automaton.ml|14 col 3| List.assoc (q,a) m.delta
  使われない
cegen.ml|237 col 30| | EVar(v,ity) -> (try EVar(List.assoc v vmap, ity) with Not_found -> eterm)
  される
conversion.ml|49 col 36| Syntax.Name(s) -> (try Var(List.assoc s vmap) with Not_found -> T(s))
  される
grammar.ml|162 col 9| List.assoc x s
  される
grammar.ml|171 col 9| List.assoc x s
  される
scc.ml|52 col 31| let (_,_,nextr) = List.assoc x g in
  される
scc.ml|57 col 20| try (let _ = List.assoc y g' in g') with
  される
scc.ml|154 col 29| let (nextr,_) = List.assoc x g in
  される
scc.ml|159 col 20| try (let _ = List.assoc y g' in g') with
  される
scc.ml|163 col 25| let (nextr, cacher) = List.assoc n g in
  使われない関数
stype.ml|55 col 21| STvar v -> (try List.assoc v sub with Not_found -> st)
  される
stype.ml|149 col 29| let lookup_stype_t a cste = List.assoc a cste
  されない @tcheck_term
utilities.ml|235 col 5| List.assoc var s
  される
utilities.ml|321 col 9| (* like List.assoc, but with a specialized equality function *)
  される

-->
