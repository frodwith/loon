/-  psur=loon-parse
/+  plib=loon-parse, clib=loon-compile, punk
=,  psur
=,  plib
=,  clib
:-  %say
|=  [^ ~ [in=$@(~ (each tape path)) stop=?(%kern %punk %nock) ~]]
:-  %noun
=/  sing
  |=  t=tang
  ~>  %slog.[0 %rose [[10 ~] "" ""] (flop t)]
  ~
?^  in
  =/  par
    %-  parse-tape
    ?~  -.in  `p.in
    =/  file  .^(mime %cx p.in)
    :-  p.in
    (trip (end [3 p.q.file] q.q.file))
  ?:  ?=(%| -.par)  (sing (pretty-parse-tape-err p.par))
  =/  ken  (~(mint uk %arg ~) p.par)
  ?:  ?=(%| -.ken)  (sing (pretty-compile-err p.ken))
  ?:  ?=(%kern stop)  kern+p.ken
  =/  p  (kp p.ken)
  ?:  ?=(%punk stop)  punk+p
  nock+(compile:punk p)
%ok
