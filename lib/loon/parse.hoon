/-  loon-parse, rsur=loon-read
/+  rlib=loon-read
=,  loon-parse
=,  rsur
=,  rlib
^?
|%
++  bach
  |*  [a=(each) f=$-(* (each))]
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
  %+  bach  one        |=  hed=b
  %+  bach  ^$(l t.l)  |=  tal=b
  &+(k hed tal)
++  june
  |=  [a=uexp b=uexp]
  ^-  uexp
  [%cons +<]
++  parse-sqar
  |*  b=mold
  |=  $:  cons=$-([b b] b)
          parse=$-(lexp (parm b))
          i=lexp
          t=(lest lexp)
      ==
  %+  bach  (parse i)               |=  hed=b
  %+  bach  (tuplify t cons parse)  |=  tal=b
  &+(cons hed tal)
++  pe
  ::  bug=& means exclude spot hints
  =|  tac=trak
  |_  bug=?
  ++  die  |=(d=desc |+[d tac])
  ::  generate a spot form if bug is off
  ::  in general, wrap this around things that can crash
  ::  (so if they do, you know where they did),
  ::  function calls, function bodies
  ++  tops
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
    %+  bach  (one-lexp args)  |=  bod=lexp
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
        %+  bach  (parse-uexp &3.exp.e)  |=  bod=uexp
        &+[~ s.exp.i.l.exp.e bod]
    ==
  ++  parse-tag
    |=  e=lexp
    ^-  (parm @)
    ?+  exp.e  (die ~)
      @          &+exp.e
      [%cord *]  &+c.exp.e
    ==
  ++  band-tup
    |=  ls=(list lexp)
    ((parse-tup band) band-cons parse-band ls)
  ++  parse-uexp  
    |=  e=lexp
    ^-  (parm uexp)
    ?-  exp.e
      @          &+litn+exp.e
      [%symb *]  &+(tops loc.e s.exp.e)
      [%tape *]  &+exp.e
      [%cord *]  &+exp.e
      [%sqar *]  =.  tac   [sqar+loc.e tac]
                 ((parse-sqar uexp) june parse-uexp +.exp.e)
      [%rond *]
        ?~  l.exp.e    (die %none)
        =*  op    i.l.exp.e
        =*  args  t.l.exp.e
        =*  b     bach
        =*  r     $
        ?.  ?=([%symb *] exp.op)
          ::  op not symbol, treat as application
          =.  tac   [appl+loc.e tac]
          %+  b  $(e op)            |=  lam=uexp
          %+  b  (parse-args args)  |=  arg=uexp
          &+(tops loc.e %appl lam arg)
        ?+  s.exp.op
          ::  default, lookup symbol and apply
          =.  tac   [appl+loc.e tac]
          %+  b  (parse-args args)  |=  arg=uexp
          &+(tops loc.e %appl s.exp.op arg)
            %bug
          (parse-bug & loc.e args)
            %debug
          (parse-bug | loc.e args)
            %'/'
          =.  tac  [frag+loc.e tac]
          ?.  ?=([[* @] * ~] args)  (die ~)
          %+  b  r(e &2.args)  |=  of=uexp
          &+(tops loc.e %frag +.&1.args of)
            %edit
          =.  tac  [edit+loc.e tac]
          ?.  ?=([[* @] * * ~] args)  (die ~)
          %+  b  r(e &2.args)  |=  tgt=uexp
          %+  b  r(e &3.args)  |=  val=uexp
          &+(tops loc.e %edit +.&1.args tgt val)
            %'+'
          =.  tac  [bump+loc.e tac]
          ?.  ?=([* ~] args)  (die ~)
          %+  b  r(e &1.args)  |=  atm=uexp
          &+(tops loc.e %bump atm)
            %'?'
          =.  tac  [deep+loc.e tac]
          ?.  ?=([* ~] args)  (die ~)
          (b r(e &1.args) |=(e=uexp &+deep+e))
            %'='
          =.  tac  [deep+loc.e tac]
          ?.  ?=([* * ~] args)  (die ~)
          %+  b  r(e &1.args)  |=  a=uexp
          %+  b  r(e &2.args)  |=  b=uexp
          &+same+a^b
            %if
          =.  tac  [cond+loc.e tac]
          ?.  ?=([* * * ~] args)  (die ~)
          %+  b  r(e &1.args)  |=  t=uexp
          %+  b  r(e &2.args)  |=  y=uexp
          %+  b  r(e &3.args)  |=  n=uexp
          &+cond+t^y^n
            %with
          =.  tac  [with+loc.e tac]
          ?.  ?=([* * * ~] args)  (die ~)
          %+  b  (parse-tram &1.args)  |=  nam=tram
          %+  b  r(e &2.args)          |=  val=uexp
          %+  b  r(e &3.args)          |=  in=uexp
          &+with+nam^val^in
            %let
          =.  tac  [let+loc.e tac]
          ?:  ?=([[* %rond *] * ~] args)
            ::  (let ((a foo) (b bar)) body) ~>
            ::  (let [a b] [foo bar] body)
            %+  b  (band-tup l.exp.i.args)  |=  arm=band
            %+  b  r(e &2.args)             |=  in=uexp
            =+  =/  a  arm
                |-  ^-  [nam=tram val=uexp]
                ?@  -.a  +.a
                =/  p  $(a p.a)
                =/  q  $(a q.a)
                [[nam.p nam.q] %cons val.p val.q]
            &+letn+nam^val^in
          ?.  ?=([* * * ~] args)  (die ~)
          %+  b  (parse-tram &1.args)  |=  nam=tram
          %+  b  r(e &2.args)          |=  val=uexp
          %+  b  r(e &3.args)          |=  in=uexp
          &+letn+nam^val^in
            %'let*'
          =.  tac  [['let*' loc.e] tac]
          ?.  ?=([[* %rond *] * ~] args)  (die ~)
          =/  pas  l.exp.i.args
          ?~  pas  (die ~)
          =|  out=(list [tram uexp])
          |-  ^-  (parm uexp)
          =*  loop  $
          ?.  ?=([* %rond * * ~] i.pas)  (die ~)
          =*  p  l.exp.i.pas
          %+  b  (parse-tram &1.p)  |=  nam=tram
          %+  b  r(e &2.p)          |=  val=uexp
          =/  hed  [nam val]
          ?~  t.pas
            %+  b  r(e &2.args)  |=  in=uexp
            =/  fin  (flop hed out)
            ?<  ?=(~ fin)
            &+lets+fin^in
          loop(pas t.pas, out [hed out])
            %rec
          =.  tac  [rec+loc.e tac]
          ?.  ?=([* * ~] args)  (die ~)
          %+  b  (parse-band &1.args)  |=  arm=band
          %+  b  r(e &2.args)          |=  in=uexp
          &+letr+arm^in
            %bind
          =.  tac  [bind+loc.e tac]
          ?.  ?=([[* %symb *] * * ~] args)  (die ~)
          %+  b  (parse-tram &2.args)  |=  to=tram
          %+  b  r(e &3.args)          |=  bod=uexp
          &+bind+[s.exp.i.args to bod]
            %fn
          =.  tac  [lamb+loc.e tac]
          ?+  args  (die ~)
            [* * ~]
              %+  b  (parse-tram &1.args)  |=  arg=tram
              %+  b  r(e &2.args)          |=  bod=uexp
              &+lamb+[%$ arg (tops loc.i.&2.args bod)]
            [[* %symb *] * * ~]
              %+  b  (parse-tram &2.args)  |=  arg=tram
              %+  b  r(e &3.args)          |=  bod=uexp
              &+lamb+[s.exp.i.args arg (tops loc.i.&3.args bod)]
          ==
            %dfn
          =.  tac  [dfn+loc.e tac]
          ?.  ?=([* * ~] args)  (die ~)
          %+  b  (parse-tram &1.args)  |=  arg=tram
          %+  b  r(e &2.args)          |=  bod=uexp
          &+delt+arg^(tops loc.i.&2.args bod)
            %'*'
          =.  tac  [nock+loc.e tac]
          ?.  ?=([* *] args)  (die ~)
          %+  b  r(e &1.args)          |=  fol=uexp
          %+  b  (parse-args +.args)   |=  arg=uexp
          &+(tops loc.e nock+fol^arg)
            %line
          =.  tac  [line+loc.e tac]
          ?.  ?=([[* %symb *] *] args)  (die ~)
          %+  b  (parse-args +.args)  |=  arg=uexp
          &+(tops loc.e line+[s.exp.i.args arg])
            %core
          =.  tac  [core+loc.e tac]
          %+  b  (band-tup args)  |=  arm=band
          &+core+arm
            %pull
          =.  tac  [pull+loc.e tac]
          ?.  ?=([[* @] * ~] args)  (die ~)
          %+  b  r(e &2.args)  |=  cor=uexp
          &+(tops loc.e pull+[exp.i.args cor])
            %sint
          =.  tac  [sint+loc.e tac]
          ?.  ?=([* * ~] args)  (die ~)
          %+  b  (parse-tag &1.args)   |=  tag=@
          %+  b  r(e &2.args)  |=  exp=uexp
          &+sint+tag^exp
            %dint
          =.  tac  [dint+loc.e tac]
          ?.  ?=([* * * ~] args)  (die ~)
          %+  b  (parse-tag &1.args)   |=  tag=@
          %+  b  r(e &2.args)          |=  clu=uexp
          %+  b  r(e &3.args)          |=  exp=uexp
          &+dint+tag^clu^exp
        ==
    ==
  --
++  parse-tape
  |=  [id=path in=tape]
  ^-  (each uexp parse-tape-err)
  =/  red  (read-tape id in)
  ?.  ?=(%& -.red)  |+&+p.red
  =/  par  (parse-uexp:pe p.red)
  ?.  ?=(%& -.par)  |+|+p.par
  &+p.par
++  rend-spot
  |=  s=spot
  ^-  tank
  =*  l   p.q.s
  =*  r   q.q.s
  :~  %rose  [":" ~ ~]
      (smyt p.s)
      :~  %rose  ["." "<" ">"] 
          :~  %rose  [" " "[" "]"]
              leaf+(scow %ud p.l)
              leaf+(scow %ud q.l)
          ==
          :~  %rose  [" " "[" "]"]
              leaf+(scow %ud p.r)
              leaf+(scow %ud q.r)
          ==
      ==
  ==
++  pretty-parse-err
  |=  err=parse-err
  =|  out=tang
  =/  in  tac.err
  :-  ?~  des.err  leaf+"parse error"
      leaf+"{<des.err>}"
  |-  ^-  tang
  ?~  in  (flop out)
  %=  $  in  t.in  out  :_  out
    :~  %rose  ["|" "" ""]
        leaf+"{<mot.i.in>}"
        ?~  loc.i.in
          leaf+"<no location>"
        (rend-spot loc.i.in)
    ==
  ==
++  pretty-parse-tape-err
  |=  e=parse-tape-err
  ^-  tang
  ?:  ?=(%& -.e)
    ~[leaf+(pretty-read-tape-err p.e)]
  (pretty-parse-err p.e)
--
