/-  loon-parse, rsur=loon-read
/+  rlib=loon-read
=,  loon-parse
=,  rsur
=,  rlib
^?
|%
::  apply a parse-errable function f to every lexp in a lest,
::  consing results with k (pattern when parsing lists to tuples)
++  tuplify
  |*  b=mold
  |=  [l=(lest lexp) k=$-([b b] b) f=$-(lexp (parm b))]
  ^-  (parm b)
  =/  heh   (f i.l)
  ?~  t.l   heh
  ?.  ?=(%& -.heh)  heh
  =/  r  $(l t.l)
  ?.  ?=(%& -.r)  r
  &+(k p.heh p.r)
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
    ^-  (parm bond)
    !!
  ++  june
    |=  [a=uexp b=uexp]
    ^-  uexp
    ?:  ?=([[%litn *] %litn *] +<)
      [%litn val.a val.b]
    [%cons +<]
  ++  parse-sqar
    |=  [i=lexp t=(lest lexp)]
    =/  hed  (parse-uexp i)
    ?.  ?=(%& -.hed)  hed
    =/  tal  ((tuplify uexp) t june parse-uexp)
    ?.  ?=(%& -.tal)  tal
    &+(june p.hed p.tal)
  ++  parse-args
    |=  arg=(list lexp)
    ^-  (parm uexp)
    ?~  arg    (die ~)
    ?~  t.arg  (parse-uexp i.arg)
    (parse-sqar arg)
  ++  one-lexp
    |=  args=(list lexp)
    ^-  (parm lexp)
    ?~  args    (die ~)
    ?~  t.args  &+i.args
    (die %many)
  ++  parse-bug
    |=  [bug=? loc=spam args=(list lexp)]
    =.  tac  [dbug+loc tac]
    =/  bod  (one-lexp args)
    ?.  ?=(%& -.bod)  bod
    (parse-uexp(bug bug) p.bod)
  ++  parse-uexp  
    |=  e=lexp
    ^-  (parm uexp)
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
          =/  lam  $(e op)
          ?.  ?=(%& -.lam)  lam
          =/  arg  (parse-args args)
          ?.  ?=(%& -.arg)  arg
          &+(wrap loc.e %appl p.lam p.arg)
        ?+  s.exp.op  =.  tac   [appl+loc.e tac]
                      =/  arg  (parse-args args)
                      ?.  ?=(%& -.arg)  arg
                      &+(wrap loc.e %appl s.exp.op p.arg)
          %bug    (parse-bug & loc.e args)
          %debug  (parse-bug | loc.e args)
          %frag   =.  tac  [frag+loc.e tac]
                  ?.  ?=([[* @] ^ ~] args)  (die ~)
                  =/  of  (parse-uexp +<.args)
                  ?.  ?=(%& -.of)  of
                  &+(wrap loc.e %frag ->.args p.of)
        ==
    ==
  ++  parse-prog
    |=  e=lexp
    ^-  (parm prog)
    =.  tac  [prog+loc.e tac]
    ?.  ?=  [* %rond [* %symb %main] *]  e
      =/  usr  (parse-uexp e)
      ?.  ?=(%& -.usr)  usr
      &+[%$ p.usr]
    =*  bod  t.l.exp.e
    ?.  ?=  [* * ~]  bod  (die ~)
    =/  bon  (parse-bond &1.bod)
    ?.  ?=(%& -.bon)  bon
    =/  usr  (parse-uexp &2.bod)
    ?.  ?=(%& -.usr)  usr
    &+[p.bon p.usr]
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
