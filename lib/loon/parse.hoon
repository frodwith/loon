/-  loon-parse, rsur=loon-read
/+  rlib=loon-read
=,  loon-parse
=,  rsur
=,  rlib
^?
|%
++  barm
  |*  [a=(parm) f=$-(* (parm))]
  ?.  ?=(%& -.a)  a
  (f p.a)
::  apply a parse-errable function f to every lexp in a lest,
::  consing results with k (pattern when parsing lists to tuples)
++  tuplify
  |*  b=mold
  |=  [l=(lest lexp) k=$-([b b] b) f=$-(lexp (parm b))]
  ^-  (parm b)
  =/  one   (f i.l)
  ?~  t.l   one
  %+  barm  one        |=  hed=b
  %+  barm  ^$(l t.l)  |=  tal=b
  &+p=(k hed tal)
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
    %+  barm  (parse-uexp i)                      |=  hed=uexp
    %+  barm  ((tuplify uexp) t june parse-uexp)  |=  tal=uexp
    &+(june hed tal)
  ++  parse-args
    |=  arg=(list lexp)
    ^-  (parm uexp)
    ::  arg can't be empty
    ?~  arg    (die %none)
    ::  but it can be a single uexp (including [... ...])
    ?~  t.arg  (parse-uexp i.arg)
    ::  or, if there are more, we will parse them as if they had []
    (parse-sqar arg)
  ++  one-lexp
    |=  args=(list lexp)
    ^-  (parm lexp)
    ?~  args    (die %none)
    ?~  t.args  &+i.args
    (die %many)
  ++  parse-bug
    |=  [bug=? loc=spam args=(list lexp)]
    =.  tac  [dbug+loc tac]
    %+  barm  (one-lexp args)  |=  bod=lexp
    (parse-uexp(bug bug) bod)
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
        ?~  l.exp.e    (die %none)
        =*  op    i.l.exp.e
        =*  args  t.l.exp.e
        ?.  ?=([%symb *] exp.op)
          =.  tac   [appl+loc.e tac]
          %+  barm  $(e op)            |=  lam=uexp
          %+  barm  (parse-args args)  |=  arg=uexp
          &+(wrap loc.e %appl lam arg)
        ?+  s.exp.op  =.  tac   [appl+loc.e tac]
                      %+  barm  (parse-args args)  |=  arg=uexp
                      &+(wrap loc.e %appl s.exp.op arg)
          %bug    (parse-bug & loc.e args)
          %debug  (parse-bug | loc.e args)
          %frag   =.  tac  [frag+loc.e tac]
                  ?.  ?=([[* @] ^ ~] args)  (die ~)
                  %+  barm  (parse-uexp +<.args)  |=  of=uexp
                  &+(wrap loc.e %frag ->.args of)
        ==
    ==
  ++  parse-prog
    |=  e=lexp
    ^-  (parm prog)
    =.  tac  [prog+loc.e tac]
    ?.  ?=  [* %rond [* %symb %main] *]  e
      (barm (parse-uexp e) |=(u=uexp &+[%$ u]))
    =*  bod  t.l.exp.e
    ?.  ?=  [* * ~]  bod  (die ~)
    %+  barm  (parse-bond &1.bod)  |=  bon=bond
    %+  barm  (parse-uexp &2.bod)  |=  usr=uexp
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
