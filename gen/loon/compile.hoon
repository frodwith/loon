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
  :_  ~
  %-  sell  !>  (~(mint uk %arg ~) p.par)
~[leaf+"ok"]
