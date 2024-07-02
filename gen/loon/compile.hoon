/-  psur=loon-parse
/+  plib=loon-parse, clib=loon-compile
=,  psur
=,  plib
=,  clib
:-  %say
|=  [^ ~ [in=tape ~]]
:-  %tang
^-  tang
?^  in
  =/  par  (parse-tape ~ in)
  ?:  ?=(%| -.par)
    (pretty-parse-tape-err p.par)
  =/  ken  (~(mint uk %arg ~) p.par)
  ?:  ?=(%| -.ken)  (pretty-compile-err p.ken)
  :_  ~  %-  sell  !>  p.ken
~[leaf+"ok"]
