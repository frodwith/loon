/-  psur=loon-parse
/+  plib=loon-parse, clib=loon-compile, punk, gut=loon-gen-utils
=,  psur
=,  plib
=,  clib
=,  gut
:-  %say
|=  [^ ~ [=path =tape stop=?(%kern %punk %nock) ~]]
:-  %noun
=/  in  (gen-input path tape)
?^  in
  =/  par  (parse-tape in)
  ?:  ?=(%| -.par)  (sing (pretty-parse-tape-err p.par))
  =/  ken  (~(mint uk %arg ~) p.par)
  ?:  ?=(%| -.ken)  (sing (pretty-compile-err p.ken))
  ?:  ?=(%kern stop)  kern+p.ken
  =/  p  (kp p.ken)
  ?:  ?=(%punk stop)  punk+p
  nock+(compile:punk p)
%ok
