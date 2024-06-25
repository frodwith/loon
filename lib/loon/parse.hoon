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
  |*  [l=(lest lexp) k=$-(^ *) f=$-(lexp (parm))]
  |-
  =/  one   (f i.l)
  ^+  one
  ?~  t.l   one
  =*  b  _?~(-.one p.one !!)
  %+  barm  one        |=  hed=b
  %+  barm  ^$(l t.l)  |=  tal=b
  &+(k hed tal)
++  boon
  |=  [a=bond b=bond]
  ^-  bond
  [%cell %$ a b]
++  june
  |=  [a=uexp b=uexp]
  ^-  uexp
  ?:  ?=([[%litn *] %litn *] +<)
    [%litn val.a val.b]
  [%cons +<]
++  bons  |=([a=barn b=barn] +<)
++  parse-sqar
  |*  b=mold
  |=  $:  cons=$-([b b] b)
          parse=$-(lexp (parm b))
          i=lexp
          t=(lest lexp)
      ==
  %+  barm  (parse i)               |=  hed=b
  %+  barm  (tuplify t cons parse)  |=  tal=b
  &+(cons hed tal)
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
  ++  parse-tup
    |*  b=mold
    |=  $:  cons=$-([b b] b)
            parse=$-(lexp (parm b))
            tup=(list lexp)
        ==
    ::  tup can't be empty
    ?~  tup  (die %none)
    ::  but it can be a single b (including [])
    ?~  t.tup  (parse i.tup)
    ::  or, if there are more, we will parse them as if they had []
    ((parse-sqar b) cons parse tup)
  ++  parse-barn
    |=  e=lexp
    ^-  (parm barn)
    =.  tac  [barn+loc.e tac]
    ?+  exp.e  (die ~)
      [%symb *]  &+s.exp.e
      [%sqar *]  ((parse-sqar barn) bons ..$ +.exp.e)
    ==
  ++  parse-bonds
    |=  ls=(list lexp)
    ^-  (parm bond)
    ((parse-tup bond) boon parse-bond ls)
  ++  parse-bond
    |=  e=lexp
    ^-  (parm bond)
    =.  tac  [bond+loc.e tac]
    ?+  exp.e  (die ~)
        [%symb *]
      &+s.exp.e
        [%sqar *]
      ((parse-sqar bond) boon ..$ +.exp.e)
        [%rond *]
      =*  r  l.exp.e
      ?+  r  (die ~)
          [[* %symb *] *]
        %+  barm  (parse-bonds t.r)  |=  tal=bond
        =*  s  s.exp.i.r
        ?-  tal
          @          (die %alias)
          [%cell *]  &+tal(n s)
          [%core *]  &+tal(n s)
        ==
          [[* %rond *] *]
        %+  barm  =.  tac  [barn+loc.i.r tac]
                  ((parse-tup barn) bons parse-barn l.exp.i.r)
        |=  bat=barn
        %+  barm  (parse-bonds t.r)  |=  pay=bond
        &+[%core %$ bat pay]
      ==
    ==
  ++  parse-args
    |=  arg=(list lexp)
    ((parse-tup uexp) june parse-uexp arg)
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
                 ((parse-sqar uexp) june parse-uexp +.exp.e)
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
