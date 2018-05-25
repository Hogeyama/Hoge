
データ型固有の述語が必要になる例

<a name = "mk_vte"></a>
### Cegen.mk_vte

```
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

```
arity = function
        | ItyQ(_) -> 0
        | ItyFun(_,_,aty) -> 1 + arity aty
```

という関数を定義すると

```
type mk_vte
  :  (vars: 'a list)
  -> {at: ity | List.length vars <= arity at }
  -> _
```

と書ける.

```
type F x = int + int * int * x
type ity = Fix F
f : F int -> int
f = [ fun _ -> 0 | fun (_,_,x) -> 1 + x ]
arity = fold_F f
```

<a name = "tyseq_mem"></a>
### Saturate.tyseq_mem

これはむりなのでは

```
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






