/-  psur=loon-parse
/+  plib=loon-parse, clib=loon-compile, punk
=,  psur
=,  plib
=,  clib
:-  %say
|=  [^ ~ [in=tape ~]]
:-  %noun
=/  sing
  |=  t=tang
  ~>  %slog.[0 %rose [[10 ~] "" ""] (flop t)]
  ~
?^  in
  =/  par  (parse-tape ~ in)
  ?:  ?=(%| -.par)  (sing (pretty-parse-tape-err p.par))
  =/  ken  (~(mint uk %arg ~) p.par)
  ?:  ?=(%| -.ken)  (sing (pretty-compile-err p.ken))
  ::p.ken
  ::(kp p.ken)
  (compile:punk (kp p.ken))
%ok
