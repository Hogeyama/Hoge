
データ型固有の述語が必要になる例

<a name = "mk_vte"></a>
### Cegen.mk_vte

```ocaml
type ity = ItyQ of state
         | ItyFun of a * b * ity
let rec mk_vte vars at =
  match at with
  | ItyQ(q) ->
      if vars=[] then
         ([], ItyQ(q))
      else assert false
  | ItyFun(_, ty, aty1) ->
      begin match vars with
      | [] -> ([], at)
      | v::vars' ->
           let (ve1, rt1) = mk_vte vars' aty1 in
             ((v, ty)::ve1, rt1)
      end
```

ここで

```ocaml
arity = function
        | ItyQ(_) -> 0
        | ItyFun(_,_,aty) -> 1 + arity aty
```

という関数を定義すると仕様は次のように書ける.

```ocaml
type mk_vte
  :  (vars: 'a list)
  -> {at: ity | List.length vars <= arity at }
  -> _
```


```ocaml
type F x = int + int * int * x
type ity = Fix F
f : F int -> int
f = [ fun _ -> 0,  fun (_,_,x) -> 1 + x ]
arity = cata f
```

<a name = "tyseq_mem"></a>
### Saturate.tyseq_mem

(Saturate.tyseq_subsumed, Saturate.tyseq_merge_tys)

```ocaml
type tyseq = TySeq of (Grammar.ty * tyseq ref) list | TySeqNil
let rec tyseq_mem tys tyseqref =
  match tys with
    [] -> true
  | ty::tys' ->
      begin match !tyseqref with
      | TySeqNil -> assert false (* size of the type sequence does not match *)
      | TySeq(tyseqlist) ->
          try
            let tyseqref1 = Utilities.assoc_eq eq_ty ty tyseqlist in
              tyseq_mem tys' tyseqref1
          with
            Not_found -> false
      end
```

tyseqは`Grammar.ty`でラベル付けされた木と考えられる．
上の関数は`tys`でラベル付けされたパスが`tyseqref`にあるかどうかを判定する．

#### depthで捉えられる？

```ocaml
min_depth : tyseq -> int = function
  | TySeqNil -> 0
  | TySeq xs = List.min @@ List.map (min_depth . deref . snd) xs

(* where *)
(f . g) x = f (g x)
deref x = !x
```

とすれば `tyseq_mem`には次の型が付くが，呼び出しが常にこの事前条件を満たしているか分からない．

<!--
ざっと見た所，tyseq_add_wo_subtyping後は満たしてないような気がする．Not_foundのケース
-->

```
type tyseq_mem
  :  (tys : Grammar.ty list)
  -> { tyseqref : tyseqref | min_depth (!tyseqref) >= List.length tys }
```

<a name = "pterm2term"></a>
### Conversion.pterm2term

```ocaml
(* syntax.ml *)
type head = Name of string
          | NT of string
          | FD of int
          | CASE of int
          | PAIR
          | DPAIR
          | FUN of string list * preterm
and preterm = PTapp of head * preterm list
(* conversion.ml *)
let rec pterm2term vmap pterm =
  (** distinguish between variables and terminal symbols **)
  match pterm with
    Syntax.PTapp(h, pterms) ->
      let h' =
        match h with
        | Syntax.Name(s) -> (try Var(List.assoc s vmap) with Not_found -> T(s))
        | Syntax.NT(s) -> NT(lookup_ntid s)
        | Syntax.FUN(_,_) -> assert false
        | Syntax.CASE(n) -> assert false
        | Syntax.FD(n) -> assert false
        | Syntax.PAIR -> assert false
        | Syntax.DPAIR -> assert false
     in
     let terms = List.map (pterm2term vmap) pterms in
     let terms' = if !(Flags.normalize) then
                    List.map normalize_term terms
                  else terms
     in
        mk_app h' terms'
```

必要な述語とそれを使った仕様

```ocaml
head_p : head -> bool
head_p = function
  | Syntax.Name(_) -> true
  | Syntax.NT(_) -> true
  | _ -> false
pterm_p : pterm -> bool
pterm_p (PTapp(h,pterms)) = head_p && List.for_all pterm_p pterms

type pterm2term : (vmap : _) -> { pterm: pterm | pterm_p pterm } -> Grammar.term
```

<a name = "make_node"></a>
### Pobdd.make_node

`node_id`を述語に書けるようにする必要

```ocaml
type bdd = Node of var * bdd * bdd * id * var list
         | Leaf of bool

let node_id = function
  | Leaf(true) -> 0
  | Leaf(false) -> 1
  | Node(_,_,_,x,_) -> x;;

let make_node (v,t1,t2) =
  let i1 = node_id t1 in
  let i2 = node_id t2 in
  let key = (v,i1,i2) in
  assert (i1 <> i2);
  try
    NodeHash.find node_hashtbl key
  with Not_found -> begin
    let i = gen_id () in
    let l1 = bdd_vars t1 in
    let l2 = bdd_vars t2 in
    let l = merge_vars l1 l2 in
    let t = Node (v,t1,t2,i,v::l) in
    NodeHash.add node_hashtbl key t;
    t
  end;;
```


