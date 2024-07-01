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
++  june
  |=  [a=uexp b=uexp]
  ^-  uexp
  ?:  ?=([[%litn *] %litn *] +<)
    [%litn val.a val.b]
  [%cons +<]
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
  ++  tops  ::  generate a spot form if bug is off
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
  ++  parse-tram
    |=  e=lexp
    ^-  (parm tram)
    =.  tac  [tram+loc.e tac]
    ?+  exp.e  (die ~)
      [%symb *]  &+s.exp.e
      [%sqar *]  ((parse-sqar tram) |=([tram tram] +<) ..$ +.exp.e)
    ==
  ++  parse-args  ::  parse the arguments to an operator
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
  ++  band-cons  |=([band band] +<)
  ++  parse-band
    |=  e=lexp
    =.  tac  [band+loc.e tac]
    ^-  (parm band)
    ?+  exp.e  (die ~)
      [%sqar *]
        ((parse-sqar band) band-cons ..$ +.exp.e)
      [%rond [* %symb *] * ~]
        %+  barm  (parse-uexp &3.exp.e)  |=  bod=uexp
        &+[~ s.exp.i.l.exp.e bod]
    ==
  ++  parse-tag
    |=  e=lexp
    ^-  (parm @)
    ?+  exp.e  (die ~)
      @          &+exp.e
      [%cord *]  &+c.exp.e
    ==
  ++  parse-uexp  
    |=  e=lexp
    ^-  (parm uexp)
    ?-  exp.e
      @          &+litn+exp.e
      [%symb *]  &+s.exp.e
      [%tape *]  &+exp.e
      [%cord *]  &+exp.e
      [%sqar *]  =.  tac   [sqar+loc.e tac]
                 ((parse-sqar uexp) june parse-uexp +.exp.e)
      [%rond *]
        ?~  l.exp.e    (die %none)
        =*  op    i.l.exp.e
        =*  args  t.l.exp.e
        ?.  ?=([%symb *] exp.op)
          ::  op not symbol, treat as application
          =.  tac   [appl+loc.e tac]
          %+  barm  $(e op)            |=  lam=uexp
          %+  barm  (parse-args args)  |=  arg=uexp
          &+(tops loc.e %appl lam arg)
        ?+  s.exp.op
          ::  default, lookup symbol and apply
          =.  tac   [appl+loc.e tac]
          %+  barm  (parse-args args)  |=  arg=uexp
          &+(tops loc.e %appl s.exp.op arg)
            %bug
          (parse-bug & loc.e args)
            %debug
          (parse-bug | loc.e args)
            %frag
          =.  tac  [frag+loc.e tac]
          ?.  ?=([[* @] * ~] args)  (die ~)
          %+  barm  (parse-uexp &2.args)  |=  of=uexp
          &+(tops loc.e %frag +.&1.args of)
            %edit
          =.  tac  [edit+loc.e tac]
          ?.  ?=([[* @] * * ~] args)  (die ~)
          %+  barm  (parse-uexp &2.args)  |=  tgt=uexp
          %+  barm  (parse-uexp &3.args)  |=  val=uexp
          &+(tops loc.e %edit +.&1.args tgt val)
            %bump
          =.  tac  [bump+loc.e tac]
          ?.  ?=([* ~] args)  (die ~)
          %+  barm  (parse-uexp &1.args)  |=  atm=uexp
          &+(tops loc.e %bump atm)
            %deep
          =.  tac  [deep+loc.e tac]
          ?.  ?=([* ~] args)  (die ~)
          (barm (parse-uexp &1.args) |=(e=uexp &+deep+e))
            %same
          =.  tac  [deep+loc.e tac]
          ?.  ?=([* * ~] args)  (die ~)
          %+  barm  (parse-uexp &1.args)  |=  a=uexp
          %+  barm  (parse-uexp &2.args)  |=  b=uexp
          &+same+a^b
            %if
          =.  tac  [cond+loc.e tac]
          ?.  ?=([* * * ~] args)  (die ~)
          %+  barm  (parse-uexp &1.args)  |=  t=uexp
          %+  barm  (parse-uexp &2.args)  |=  y=uexp
          %+  barm  (parse-uexp &3.args)  |=  n=uexp
          &+cond+t^y^n
            %with
          =.  tac  [with+loc.e tac]
          ?.  ?=([* * * ~] args)  (die ~)
          %+  barm  (parse-tram &1.args)  |=  nam=tram
          %+  barm  (parse-uexp &2.args)  |=  val=uexp
          %+  barm  (parse-uexp &3.args)  |=  in=uexp
          &+with+nam^val^in
            %let
          =.  tac  [let+loc.e tac]
          ?.  ?=([* * * ~] args)  (die ~)
          %+  barm  (parse-tram &1.args)  |=  nam=tram
          %+  barm  (parse-uexp &2.args)  |=  val=uexp
          %+  barm  (parse-uexp &3.args)  |=  in=uexp
          &+letn+nam^val^in
            %rec
          =.  tac  [rec+loc.e tac]
          ?.  ?=([* * ~] args)  (die ~)
          %+  barm  (parse-band &1.args)  |=  arm=band
          %+  barm  (parse-uexp &2.args)  |=  in=uexp
          &+letr+arm^in
            %bind
          =.  tac  [bind+loc.e tac]
          ?.  ?=([[* %symb *] * * ~] args)  (die ~)
          %+  barm  (parse-tram &2.args)  |=  to=tram
          %+  barm  (parse-uexp &3.args)  |=  bod=uexp
          &+bind+[s.exp.i.args to bod]
            %fn
          =.  tac  [lamb+loc.e tac]
          ?+  args  (die ~)
            [* * ~]
              %+  barm  (parse-tram &1.args)  |=  arg=tram
              %+  barm  (parse-uexp &2.args)  |=  bod=uexp
              &+lamb+[%$ arg bod]
            [[* %symb *] * * ~]
              %+  barm  (parse-tram &2.args)  |=  arg=tram
              %+  barm  (parse-uexp &3.args)  |=  bod=uexp
              &+lamb+[s.exp.i.args arg bod]
          ==
            %dfn
          =.  tac  [dfn+loc.e tac]
          ?.  ?=([* * ~] args)  (die ~)
          %+  barm  (parse-tram &1.args)  |=  arg=tram
          %+  barm  (parse-uexp &2.args)  |=  bod=uexp
          &+delt+arg^bod
            %nock
          =.  tac  [nock+loc.e tac]
          ?.  ?=([* *] args)  (die ~)
          %+  barm  (parse-uexp &1.args)  |=  fol=uexp
          %+  barm  (parse-args +.args)   |=  arg=uexp
          &+nock+fol^arg
            %core
          =.  tac  [core+loc.e tac]
          %+  barm  ((parse-tup band) band-cons parse-band args)
          |=  arm=band  &+core+arm
            %pull
          =.  tac  [pull+loc.e tac]
          ?.  ?=([[* @] * ~] args)  (die ~)
          %+  barm  (parse-uexp &2.args)  |=  cor=uexp
          &+pull+[exp.i.args cor]
            %sint
          =.  tac  [sint+loc.e tac]
          ?.  ?=([* * ~] args)  (die ~)
          %+  barm  (parse-tag &1.args)   |=  tag=@
          %+  barm  (parse-uexp &2.args)  |=  exp=uexp
          &+sint+tag^exp
            %dint
          =.  tac  [dint+loc.e tac]
          ?.  ?=([* * * ~] args)  (die ~)
          %+  barm  (parse-tag &1.args)   |=  tag=@
          %+  barm  (parse-uexp &2.args)  |=  clu=uexp
          %+  barm  (parse-uexp &3.args)  |=  exp=uexp
          &+dint+tag^clu^exp
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
    %+  barm  (parse-tram &1.bod)  |=  bus=tram
    %+  barm  (parse-uexp &2.bod)  |=  exp=uexp
    &+[bus exp]
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
