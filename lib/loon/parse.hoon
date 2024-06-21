/-  loon-parse, rsur=loon-read
/+  rlib=loon-read
=,  loon-parse
=,  rsur
=,  rlib
^?
|%
++  burr
  |*  r=mold
  |*  a=mold
  |=  [a=(parm a) f=$-(a (parm r))]
  ?~(-.a (f p.a) a)
::  apply a parse-errable function f to every lexp in a lest,
::  consing results with k (pattern when parsing lists to tuples)
++  tuplify
  |*  b=mold
  |=  [l=(lest lexp) k=$-([b b] b) f=$-(lexp (parm b))]
  =/  heh   (f i.l)
  ?~  t.l   heh
  ;<  h=b  (burr b)  heh
  ;<  r=b  (burr b)  ^$(l t.l)
  &+(k h r)
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
    ;<  hed=uexp  (burr uexp)  (parse-uexp i)
    ;<  tal=uexp  (burr uexp)  ((tuplify uexp) t june parse-uexp)
    &+(june hed tal)
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
    ^-  (parm uexp)
    =.  tac  [bug+loc tac]
    ;<  bod=lexp  (burr uexp)  (one-lexp args)
    =.  ^bug  bug
    (parse-uexp bod)
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
          ;<  lam=uexp  (burr uexp)  $(e op)
          ;<  arg=uexp  (burr uexp)  (parse-args args)
          &+(wrap loc.e %appl lam arg)
        ?+  s.exp.op  =.  tac   [appl+loc.e tac]
                      ;<  arg=uexp  (burr uexp)  (parse-args args)
                      &+(wrap loc.e %appl s.exp.op arg)
          %bug    (parse-bug & loc.e args)
          %debug  (parse-bug | loc.e args)
        ==
    ==
  ++  parse-prog
    |=  e=lexp
    ^-  (parm prog)
    =.  tac  [prog+loc.e tac]
    ?.  ?=  [* %rond [* %symb %main] *]  e
      ;<  usr=uexp  (burr prog)  (parse-uexp e)
      &+[%$ usr]
    =*  bod  t.l.exp.e
    ?.  ?=  [* * ~]  bod  |+main-args+tac
    ;<  bon=bond  (burr prog)  (parse-bond &1.bod)
    ;<  usr=uexp  (burr prog)  (parse-uexp &2.bod)
    &+[bon usr]
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
