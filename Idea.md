

ADTの関数エンコードに起因する問題
=================================

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
    + 述語発見
        + Recursive Data Typesのときと同じ問題


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

```
ref := v          ==> assume (P v)
let x = !ref in e ==> let x = * in assume (P v); [[e]]
```

`P`をCEGAR mannarで強めたり弱めたりする


### どのくらい有効か

述語`P`がうまく行きさえすれば[`Ai.merge_statevecs`](./Reference-Hashtbl-Array.md#Ai__merge_statevecs)はこれで検証できるようになるはず．



### Stoe-Passing Style


