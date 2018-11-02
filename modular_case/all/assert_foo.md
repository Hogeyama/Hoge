
+ `Cegen.evaluate_eterm`
    + `(ItyQ(q1),ItyQ(q2)) -> assert (q1=q2); evaluate_eterm t env`
    + 難しい

+ `Pobdd.make_node`
    + `assert (node_id t1 <> node_id t2)`
    + callerは以下．どれも複雑で難しい
        + go
        + bdd_(or|and|...)

+ `Pobdd.restrict_sorted`
    + `assert (sorted (List.map (function POS v | NEG v -> v) vl));`
    + sorted

