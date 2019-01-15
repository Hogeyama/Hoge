
List Non-empty
==============

<a name = "Main__report_breakdown"></a>

Main.report_breakdown
---------------------

```ocaml
let times : float list ref = ref []

let report_breakdown start_t end_t =
  let ts = !times in
  let last = if ts=[] then start_t else List.hd ts in
  let start = ref start_t in
  List.iter
    (fun t ->
      print_string ("  checkpoint: "^(string_of_float (t -. !start))^"sec\n");
      start := t)
    (List.rev ts);
  print_string ("  checkpoint: "^(string_of_float (end_t -. last))^"sec\n")
```

+ main.mlの先頭に次を加えればwhole verificationが通る:

  ````ocaml
  (*{SPEC}
    external List.hd : float |len:len>0| list -> float
  {SPEC}*)

  ````

  ````
  Sub-problem 1/2:
  Safe!

  Sub-problem 2/2:
  Safe!

  CEGAR-cycles: 6
  total: 331.347 sec
    abst: 307.141 sec
    mc: 4.778 sec
    refine: 13.742 sec
  ````

+ コミットしていない修正が必要


List same length
================


<a name = "Utilities__inexlist"></a>

Utilities.indexlist
-------------------

```ocaml
let rec fromto m n =
  if m>=n then [] else m::(fromto (m+1) n);;

let indexlist l =
  let len = List.length l in
  let indices = fromto 0 len in
  List.combine indices l

let indexlistr l =
  let len = List.length l in
  let indices = fromto 0 len in
  List.combine l indices
```

List.combineのspecを書いてutilities.mlを打ち切れば通る


