
<a name = "register_nt"></a>
### Conversion.register_nt

+ HorSat2への入力次第では`DuplicatedNonterminal`の送出が避けられない

```ocaml
type register_nt
  :  { ntname : string | not (Hashtbl.mem ntname tab_ntname2id) }
  -> unit
let register_nt ntname =
  if Hashtbl.mem tab_ntname2id ntname then raise (DuplicatedNonterminal ntname)
  else
    let nt = new_nt() in
      Hashtbl.add tab_ntname2id ntname nt;
      (!nttab).(nt) <- (ntname,O) (* for the moment, ignore the kind *)
```

<a name = "lookup_ntid"></a>
### Conversion.lookup_ntid

+ HorSat2への入力次第では`UndefinedNonterminal`の送出が避けられない

```ocaml
type lookup_ntid
  :  { ntname : string | Hashtbl.mem ntname tab_ntname2id }
  -> Grammar.nameNT
let lookup_ntid ntname =
  try Hashtbl.find tab_ntname2id ntname
  with Not_found ->
      raise (UndefinedNonterminal ntname)
```


