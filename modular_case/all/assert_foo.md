
+ `Cegen.evaluate_eterm`: `(ItyQ(q1),ItyQ(q2)) -> assert (q1=q2); evaluate_eterm t env`

    + 無理そう

+ `Pobdd.make_node`: `assert (node_id t1 <> node_id t2)`

    + 無理そう
    + callerはどれも厳しい
        + go
        + bdd_(or|and|...)

+ `Pobdd.restrict_sorted`: `assert (sorted (List.map (function POS v | NEG v -> v) vl));`

    + 無理そう
    + sorted

