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
  ^-  (parm b)
  %+  bach  (parse i)    |=  one=b
  |-  ^-  (parm b)
  %+  bach  (parse i.t)  |=  hed=b
  ?~  t.t  &+(cons one hed)
  %+  bach  ^$(t t.t)    |=  tal=b
  &+(cons one (cons hed tal))
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
  ++  parse-list
    |*  b=mold
    =|  out=(list b)
    |=  [parse=$-(lexp (parm b)) src=(list lexp)]
    ^-  (parm (list b))
    ?~  src  &+(flop out)
    %+  bach  (parse i.src)  |=  p=b
    ^$(src t.src, out [p out])
  ++  parse-lest
    |*  b=mold
    |=  [parse=$-(lexp (parm b)) src=(lest lexp)]
    ^-  (parm (lest b))
    %+  bach  (parse i.src)                 |=  i=b
    %+  bach  ((parse-list b) parse t.src)  |=  t=(list b)
    &+[i t]
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
  ++  parse-cases
    |*  h=mold
    |=  [parse=$-(lexp (parm h)) l=(list lexp)]
    =|  out=(list [h uexp])
    |-  ^-  (parm [(lest [h uexp]) (unit uexp)])
    =*  loop  $
    ?~  l  =/  tou  (flop out)
           ?~  tou  (die %none)
           &+[tou ~]
    =.  tac  [case+loc.i.l tac]
    ?.  ?=([* %rond * * ~] i.l)  (die ~)
    =*  ele  l.exp.i.l
    ?.  ?=([[* %symb *] * ~] ele)
      %+  bach  (parse &1.ele)       |=  hed=h
      %+  bach  (parse-uexp &2.ele)  |=  bod=uexp
      loop(l t.l, out [[hed bod] out])
    ?.  ?=(%$ s.exp.i.ele)  (die ~)
    ?^  t.l  (die %else)
    =/  tou  (flop out)
    ?~  tou  (die %none)
    %+  bach  (parse-uexp &2.ele)  |=  bod=uexp
    &+[tou `bod]
  ++  parse-lit
    |=  e=lexp
    =.  tac  [lit+loc.e tac]
    ^-  (parm *)
    =*  x  exp.e
    ?+  x  (die ~)
      @          &+x
      [%tape *]  &+t.x
      [%cord *]  &+c.x
      [%sqar *]  ((parse-sqar *) |=(^ +<) ..$ +.x)
    ==
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
  ++  parse-sent
    |=  e=lexp
    ^-  (parm sent)
    =.  tac   [sent+loc.e tac]
    ?.  ?=([* %rond * * ~] e)  (die ~)
    =*  l  l.exp.e
    %+  bach  (parse-tram &1.l)  |=  sub=tram
    %+  bach  (parse-uexp &2.l)  |=  ped=uexp
    &+[sub ped]
  ++  parse-page
    |=  e=lexp
    ^-  (parm page)
    =.  tac   [page+loc.e tac]
    ?.  ?=([* %sqar *] e)
      (bach (parse-sent e) |=(s=sent &+`s))
    ((parse-sqar page) |=([page page] +<) parse-page +.exp.e)
  ++  parse-book
    |=  e=lexp
    =.  tac   [book+loc.e tac]
    ?.  ?=([* %rond *] e)  (die ~)
    ?~  l.exp.e  (die %none)
    ((parse-lest page) parse-page l.exp.e)
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
          =.  tac  [if+loc.e tac]
          ?.  ?=([* * * ~] args)  (die ~)
          %+  b  r(e &1.args)  |=  t=uexp
          %+  b  r(e &2.args)  |=  y=uexp
          %+  b  r(e &3.args)  |=  n=uexp
          &+if+t^(tops loc.i.&2.args y)^(tops loc.i.&3.args n)
            %cond
          =.  tac  [cond+loc.e tac]
          %+  b  ((parse-cases uexp) parse-uexp args)
          |=  [col=cole els=(unit uexp)]
          &+cond+col^els
            %case
          =.  tac  [case+loc.e tac]
          ?.  ?=([[* %symb *] *] args)  (die ~)
          =*  foc  s.exp.i.args
          %+  b  ((parse-cases *) parse-lit t.args)
          |=  [doz=doze els=(unit uexp)]
          &+case+foc^doz^els
            %with
          =.  tac  [with+loc.e tac]
          ?.  ?=([* * * ~] args)  (die ~)
          %+  b  (parse-tram &1.args)  |=  nam=tram
          %+  b  r(e &2.args)          |=  val=uexp
          %+  b  r(e &3.args)          |=  in=uexp
          &+with+nam^val^in
            %let
          =.  tac  [let+loc.e tac]
          ?.  ?=([* * ~] args)  (die ~)
          %+  b  (parse-page &1.args)  |=  p=page
          %+  b  r(e &2.args)          |=  in=uexp
          &+letn+p^in
            %'let*'
          ?.  ?=([* * ~] args)  (die ~)
          %+  b  (parse-book &1.args)  |=  bok=book
          %+  b  r(e &2.args)          |=  in=uexp
          &+lets+bok^in
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
            %'~'
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
