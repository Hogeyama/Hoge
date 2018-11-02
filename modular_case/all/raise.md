
+ `Cegen.find_derivation`: `raise (Found eterm2)`

    + catched

+ `Cegen.find_derivation`: `head_typings; raise Not_found`

    + catched

+ `Cegen.find_derivation_terms`: `ItyQ(_) -> raise Not_found`

    + catched

+ `Conversion.register_nt`: `if Hashtbl.mem tab_ntname2id ntname then raise (DuplicatedNonterminal ntname)`

    + HorSat2への入力次第で起こりうるエラー（仕方ない）

+ `Conversion.lookup_ntid`: `with Not_found -> raise (UndefinedNonterminal ntname)`

    + 同上

+ `Conversion.insert_rank`: `else if x=0 then if k=k' then alpha else raise (InconsistentArity a)`

    + 同上

+ `Main.create_file`: `(print_string "Cannot open a log file\n"; raise LogFile)`

    + IOエラー（仕方ない）

+ `Saturate.tyseq_rem_subtyping_aux`: `[] -> raise TySeqEmptied`

    + TySeq系は無理
        + `type tyseq = TySeq of (Grammar.ty * (tyseq ref)) list | TySeqNil`

+ `Saturate.tyseq_rem_subtyping_aux`: `then if tyseqlist1=[] && tyseqlist_not_subsumed=[] then raise TySeqEmptied`

    + 同上

+ `Saturate.dequeue_var_ty_gen`: `[] -> raise WorklistVarTyEmpty`

    + catched

+ `Saturate.dequeue_nt_ty` `[] -> raise WorklistVarTyEmpty`

    + catched

+ `Saturate.pick_vte`: `with Not_found -> raise Untypable`

    + `List.find`で難しい
    + UntypableはいつCatchされるのか追えていない

+ `Saturate.check_ty_of_term`: `with Not_found -> raise Untypable`

    + `List.find`で難しい

+ `Saturate.check_ty_of_term`

    + `List.exists`

+ `Saturate.`: `else raise Untypable`

    + `List.find`

+ `Saturate.check_ty_of_term`: `else raise Untypable`

    + `List.exists`


+ `Saturate.`: `else raise Untypable`

    + `List.exists`

+ `Saturate.ml` : `[] -> raise Untypable`

+ `Saturate.ml`: |933 col 22| `if ty1=[] then raise Untypable`

+ `Saturate.ml`: |940 col 11| `[] -> raise Untypable`

    + ちょっとUntypableのときの動き方がわからないので放置するか．多分無理だと思うし

saturate.ml|1017 col 38| if nt=0 && id_of_ity ity=0 then raise REFUTED else ())
  これもわからんので
saturate.ml|1301 col 11| [] -> raise WorklistBindingEmpty
  これもわからんので

+ `Scc.split_list_at`: `[] -> raise Impossible`

    + `List.mem`

+ `Scc.find_cycle_next`: `raise Cycle`

    + 名前からして無理

+ `Setqueue.dequeue`: `[] -> raise Empty`

    + reference

+ `Stype.unify_sty`: `then raise (UnifFailure (sty1',sty2'))`

    + catchされない
    + tcheck -> unify_all -> unify_sty -> raise ...
      という流れ．入力しだいで起こりうるので無理...

+ `Stype.unify_sty`: `raise (UnifFailure (sty1,sty2))`

    + 同上

+ `Stype.tcheck`: `_ -> raise (UnifFailure (sty1,sty2))`

    + 同上

+ `Stype.tcheck` `raise (IllSorted "Rules are not well-sorted\n")`

    + 同上（ほんまか？）

List.findは三箇所で使われているがどれもNot_foundがcatchされる
