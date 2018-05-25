
述語の中でパターンマッチができればよいもの．

```ocaml
type foo = Foo of int | Bar of bool
```

に対して次のようなrefinement typeが書ければよい．

```
{ f : foo | is_Foo f && un_Foo f > 0 ||
            is_Bar f && not (un_Bar f) }
```

<a name = "mk_ehead"></a>
### Cegen.mk_ehead

単純なパターンマッチ

```ocaml
type mk_ehead
  :  { h : Grammar.term | is_T h || is_Var h }
  -> Grammar.ity
  -> eterm
let mk_ehead h aty =
  match h with
    T(a) -> ET(a,aty)
  | Var(x) -> EVar(x,aty)
  | _ -> assert false
```

<a name = "expand_varheadnode"></a>
### Ai.expand_varheadnode

参照のderef後にパターンマッチ

```ocaml
type expand_varheadnode
  :  head * termid list
  -> { node : ((head * termid list) * states) ref
     | is_Hvar (fst (fst !node))
     }
  -> unit
let expand_varheadnode term node =
  let ((h,termss),qs) = !node in
    match h with
    | Hvar(x) ->
        let (h',terms) = term in
          enqueue_node ((h', terms@termss),qs)
    | _ -> assert false
```

<a name = "nt_in_term_with_linearity"></a>
### Ai.nt_in_term_with_linearity

`nt_in_term_with_linearity`自身は全域関数．`App`のケースで呼び出す
`Grammar.decompose_term`が`App(_,_)`の形のtermを返さないことを示す必要がある．

```ocaml
type nt_in_term_with_linearity
  :  Grammar.term -> Grammar.nameNT list * Grammar.nameNT list
let rec nt_in_term_with_linearity term =
   match term with
     Var(_) -> ([], [])
   | T(_) ->  ([], [])
   | NT(f) -> ([f], [])
   | App(_,_) ->
      let (h,terms) = Grammar.decompose_term term in
        begin match h with
        | NT(f) -> let nts = nt_in_terms terms in
                    if List.mem f nts then ([],nts)
                    else ([f],nts)
        | Var(_) -> ([], nt_in_terms terms)
        | T(a) ->
            let linearity_info = Hashtbl.find tab_linearity a in
              nt_in_terms_with_linearity terms linearity_info 0 ([],[])
        | _ -> assert false
        end

(* grammar.ml *)
type decompose_term
  :  term
  -> { (t,ts) : term * term list | not (is_App t) }
let rec decompose_term t =
  match t with
  | (NT(_)|T(_)|Var(_)) -> (t, [])
  | App(t1,t2) ->
     let (h,ts)=decompose_term t1 in (h,ts@[t2])
```

<a name = "string_of_path"></a>
### Cegem.string_of_path

```ocaml
type find_nonbot
  : tree list -> { i: int | i > 0 } -> { (r, t) : int * tree | r = 0 || is_Node t }
let rec find_nonbot tl i =
  match tl with
  | [] -> (0, Bottom)
  | t::tl' ->
      match t with
      | Bottom -> find_nonbot tl' (i+1)
      | Node(_,_) -> (i, t)

type string_of_path : { t : tree | is_Node t } -> string
let rec string_of_path t =
  match t with
  | Node(a,tl) ->
      let (i,t') = find_nonbot tl 1 in
        if i=0 then ("("^a^",0)")
        else "("^a^","^(string_of_int i)^")"^(string_of_path t')
  | _ -> assert false
```

