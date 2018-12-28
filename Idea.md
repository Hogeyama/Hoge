
ADTのエンコード周りの問題
=========================

size function
-------------

### 概要

[ADT.md](./ADT.md)

### アイデア

#### size functionをユーザーに宣言させる

```ocaml
type typ =
  | O
  | Arr of typ * typ

(*{SPEC} measure arity : typ -> int {SPEC}*)
let rec arity = function
  | O -> 0
  | Arr(arg_ty, ret_ty) -> 1 + arity ret_ty
```

```ocaml
(*{SPEC}
type mk_env
  :  (l : int list)
  -> { ty : typ | List.length l <= arity ty }
  -> (int * typ) list
{SPEC}*)
let rec mk_env (xs : int list) ty = match (xs, ty) with
  | [], _ -> []
  | x::xs, Arr(arg_ty, ret_ty) -> (x,arg_ty) :: mk_env xs ret_ty
  | _ -> assert false
```

  | arityを持ち回すように変換
  v

```ocaml
let rec mk_env (len,xs) (ar,ty) = match (xs, ty) with
  | [], _ -> assume (len=0); []
  | x::(len',xs), Arr(arg_ty, (ar', ret_ty)) ->
      assume (len = len' + 1);
      assume (ar = ar' + 1);
      (x,arg_ty) :: mk_env xs ret_ty
  | _, O -> assume (ar = 0); assert false

let main (len,xs) (ar,ty) =
  assume (len <= ar);
  let _ = mk_env (len,xs) (ar,ty) in
  ()
```

##### 有効性

caller側でグローバル変数に関する推論が必要になる例ばかりでHorSatのコードで有効性を試すのは難しそう


非決定性
--------

### 概要

τをADTとし，関数`f: τ -> unit`が任意の入力に対してfailしないことを示したいとする．
現在のMoCHiは次のことを行う．

+ τ型を関数型τ'にエンコードする
+ τ'型の関数`g`をランダムに生成し，`f' g'`がfailしないことを示す．

τ型の値をτ'型の関数にエンコードした場合，エンコード後の関数は常に決定的な関数になるが，
決定的な関数のみをランダムに生成することはできないため不完全になってしまう．

### アイデア

#### ヘッドの要素は別に持つ（実装済み（佐藤先生））

+ Cons
    + 2段以上のマッチングには対応できない

#### Background Theory に Recursive Data Type を追加

+ Pros
    + 非決定的でなくなる
+ Cons
    + 述語発見
        + Interpolant solver がない？
        + CHC solverも十分な性能のものはない（？）

TODO 仮に述語発見ができたとしてどれくらい検証できるか調べる


リストのメンバーシップ
======================

アイデア
--------

### Set theoryを加える

+ Cons
    <!-- + A New Fast Tableau-Based Decision Procedure for an Unquantified Fragment of Set Theory -->
    + 述語抽象化
        + SMTがdecidableでない
            + TODO decidableなfragmentで十分か調べる
            + LiquidTypeみたいに強く制限（固定）してもよいのでは
                + membershipだけでも
    + 述語発見
        + Recursive Data Typesのときと同じ問題


### 寺尾さんの手法で扱える例があるか確認

「`term`に表れる全ての変数`v`について`List.mem_assoc v env`」という推論が必要なものばかりでとてもできそうにない

<!--
+ A New Fast Tableau-Based Decision Procedure for an Unquantified Fragment of Set Theory
+ Deepak Kapur, Rupak Majumdar, and Calogero G. Zarba. Interpolation for data structures. In Proc. SIGSOFT FSE. ACM, 2006.
    + EUF+LAでset, multisetのinterpolationができるらしい
+ A Data-Driven CHC Solver
    + Princetonで紹介してもらったやつ
+ Solving Constrained Horn Clauses with SMT
    + https://arieg.bitbucket.io/pdf/satsmtar-school-2018.pdf
-->


Reference
=========

アイデア
--------

### 非決定的な値とみなす

各Reference `ref`に述語`P`を割り当てて，書き込みと読み出しを次のように変換する．

```ocaml
ref := v          ==> assume (P v)
let x = !ref in e ==> let x = * in assume (P v); [[e]]
```

`P`をCEGAR mannerで強めたり弱めたりする


### どのくらい有効か

述語`P`がうまく行きさえすれば[`Ai.merge_statevecs`](./Reference-Hashtbl-Array.md#Ai__merge_statevecs)はこれで検証できるようになるはず．


### Store-Passing Style

+ うまく行きそうなケースはあるか
+ それを自動で判定してstore-passingに書き換えることはできるか

