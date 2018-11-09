
入力次第で起こりうるエラー
==========================

+ `Conversion.register_nt`
  + `raise (DuplicatedNonterminal ntname)`

+ `Conversion.lookup_ntid`
  + `raise (UndefinedNonterminal ntname)`

+ `Conversion.insert_rank`
  + `raise (InconsistentArity a)`

+ `Stype.tcheck`
  + `raise (IllSorted "Rules are not well-sorted\n")`

