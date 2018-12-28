
# HorSat2の分析

+ [検証できる](./ReallyPossible.md)
    + 0ケース
+ [自動化できそうな変換によって検証できる形に落とし込めるケース](./Potential1.md)
    + 5ケース
+ [自動化できそうな変換によって検証できる形に落とし込めるように見えたけどうまく行ってないケース](./Potential2.md)
    + 13ケース
+ [ちょっと難しいケース](./Level3.md)
    + 9ケース
+ [参照・Hashtbl・配列](./Reference-Hashtbl-Array.md)
    + 18ケース以上
+ [リストのメンバーシップ等](./ListMembership.md)
    + 18ケース以上
        + `List.assoc`: 12ケース以上
        + `List.find`: 6ケース以上
+ [ADT](./ADT.md)
    + 17ケース以上
        + size function等: 5ケース
        + list is_sorted: 1ケース
        + リストの長さが等しいリスト: 7ケース
        + その他: 3ケース
+ [その他](./Others.md)
    + 特に手が付けられなさそうな問題
    + 4ケース
        + Invariantがどこで保証されているか分からない: 2ケース
            <!-- + TODO elim_fun_from_*を追加 -->
        + Parserの検証が必要: 2ケース

