/-  loon-parse, rsur=loon-read
/+  rlib=loon-read
=,  loon-parse
=,  rsur
=,  rlib
^?
=>  |%
    +$  purr  (each uexp parse-err)  ::  parse-uexp result
    --
|%
++  burr
  |*  [a=(each * parse-err) f=$-(* (each * parse-err))]
  ?~(-.a (f p.a) a)
++  tump  ::  tuple map
  |*  [a=mold b=mold]
  |=  [l=(lest a) k=$-([b b] b) f=$-(a b)]
  ^-  b
  =/  h  (f i.l)
  ?~  t.l  h
  (k h $(l t.l))
++  pe
  ::  bug=& means exclude spot hints
  =|  tac=trak
  |_  bug=?
  ++  die  |=(d=desc |+[d tac])
  ++  wrap
    |=  [loc=spam u=uexp]
    ^-  uexp
    ?:  |(bug ?=(~ loc))  u
    [%spot loc u]
  ++  parse-bond
    |=  e=lexp
    ^-  (each bond parse-err)
    !!
  ++  puns  ::  purr-cons
    |=  [a=purr b=purr]
    ^-  purr
    ?~(-.a ?~(-.b &+[%cons p.a p.b] |+p.b) |+p.a)
  ++  parse-sqar
    |=  [i=lexp t=(lest lexp)]
    %+  puns  (parse-uexp i)
    ((tump lexp purr) t puns parse-uexp)
  ++  parse-args
    |=  arg=(list lexp)
    ^-  purr
    ?~  arg    (die ~)
    ?~  t.arg  (parse-uexp i.arg)
    (parse-sqar arg)
  ++  one-lexp
    |=  args=(list lexp)
    ^-  (each lexp parse-err)
    ?~  args    (die ~)
    ?~  t.args  &+i.args
    (die %many)
  ++  parse-bug
    |=  [bug=? loc=spam args=(list lexp)]
    ^-  purr
    =.  tac  [bug+loc tac]
    %+  burr  (one-lexp args)  |=  bod=lexp
    =.  ^bug  bug
    (parse-uexp bod)
  ++  parse-uexp  
    |=  e=lexp
    ^-  purr
    =.  tac  [uexp+loc.e tac]
    ?+  exp.e  (die ~)
      @          &+litn+exp.e
      [%symb *]  &+s.exp.e
      [%sqar *]  =.  tac   [sqar+loc.e tac]
                 (parse-sqar +.exp.e)
      [%rond *]
        ?~  l.exp.e    (die ~)
        =*  op    i.l.exp.e
        =*  args  t.l.exp.e
        ?.  ?=([%symb *] exp.op)
          =.  tac   [appl+loc.e tac]
          %+  burr  $(e op)            |=  lam=uexp
          %+  burr  (parse-args args)  |=  arg=uexp
          &+(wrap loc.e %appl lam arg)
        ?+  s.exp.op  =.  tac   [appl+loc.e tac]
                      %+  burr  (parse-args args)  |=  arg=uexp
                      &+(wrap loc.e %appl s.exp.op arg)
          %debug  (parse-bug | loc.e args)
          %bug    (parse-bug & loc.e args)
        ==
    ==
  ++  parse-prog
    |=  e=lexp
    ^-  (each prog parse-err)
    =.  tac  [prog+loc.e tac]
    ?.  ?=  [* %rond [* %symb %main] *]  e
      %+  burr  (parse-uexp e)  |=  usr=uexp
      &+[%$ usr]
    =*  bod  t.l.exp.e
    ?.  ?=  [* * ~]  bod  |+main-args+tac
    %+  burr  (parse-bond &1.bod)  |=  bon=bond
    %+  burr  (parse-uexp &2.bod)  |=  usr=uexp
    &+`prog`[bon usr]
  --
++  parse-tape
  |=  [id=path in=tape]
  ^-  (each prog parse-tape-err)
  =/  red  (read-tape id in)
  ?.  ?=(%& -.red)  |+&+p.red
  =/  par  (parse-prog:pe p.red)
  ?.  ?=(%& -.par)  |+|+p.par
  &+p.par
--
