/+  punk
=~
::  the lambda-delta calculus is an augmentation of the untyped lambda calculus.
::  we start with abstraction and application (lamb/appl), and we add:
::    nouns (cons,1,3,4,5,10)
::    let (8 - the subject is a tree of bound values)
::    if-then-else (6)
::    hints (11)
::    delta abstraction and application (quasiquotes lambdas, delt/nock)
::      Delta abstractions are nock formulas.
::      It is legal to delta apply a noun (see the nock spec for semantics).
::  we compile to nock through punk, the quasiquote-nock.
|%
+$  token
  $@  ?(%'(' %')' %'[' %']')
  $%  [%sym @t]
      [%num @]
      [%tap tape]
      [%cor cord]
  ==
+$  sloc  [lin=@ col=@]
+$  noken  [tok=token loc=sloc]
+$  noke-state
  $@  ~
  [?(%sym %num %tap %tae %cor %coe) beg=sloc pen=(list @t)]
+$  noke-err
  $:  chr=@tD
      loc=sloc
  ==
+$  parse-err
  $:  tag=?(%empty-tram %single-tram %bad-tram)
      loc=sloc
  ==
+$  read-nokens-err
  $@  ?(%none %many)
  $%  [%pope loc=sloc]
      [%bope loc=sloc]
      [%clop loc=sloc]
      [%clob loc=sloc]
      [%cbwp b=sloc p=sloc]
      [%cpwb p=sloc b=sloc]
  ==
+$  toke-state
  $@  ~
  [?(%sym %num %tap %tae %cor %coe) (list @t)]

+$  nexp
  $:  $=  exp
      $@  @
      $%  [%sym @t]
          [%tape tape]
          [%rond (list nexp)]
          [%sqar (list nexp)]
      ==
      loc=sloc
  ==
+$  sexp
  $@  @
  $%  [%sym @t]
      [%tape tape]
      [%rond (list sexp)]
      [%sqar (list sexp)]
  ==
+$  tram
  $@  @t
  [n=@t l=tram r=tram]
+$  neet
  $@  @t
  [p=neet q=neet]
+$  bond
  $@  @t
  $%  [%cell n=@t l=bond r=bond]
      [%core bat=neet pay=bond]
  ==
+$  fond
  $?  [%leg leg=@]
      [%arm rec=@ arm=@]
  ==
+$  fund  $@(~ fond)
+$  path  $@(~ [del=@ f=fond])
+$  gamma  (lest bond)
+$  raph
  $^  [p=raph q=raph]
  [~ nam=@t exp=user]
+$  prog
  [arg=tram exp=user]
+$  user
  $~  %a
  $@  @t
  $%  [%cons p=user q=user]
      [%frag axe=@ of=user]
      [%edit axe=@ tgt=user val=user]
      [%litn val=*]
      [%bump atm=user]
      [%deep val=user]
      [%same a=user b=user]
      [%cond t=user y=user n=user]
      [%peer nam=tram at=user in=user]
      [%letn nam=tram val=user in=user]
      [%rlet g=raph in=user]
      [%lamb arg=tram bod=user]
      [%recl nam=@t arg=tram bod=user]
      [%appl lam=user arg=user]
      [%delt arg=tram bod=user]
      [%nock fol=user arg=user]
      [%core g=raph]
      [%pull axe=@ cor=user]
      [%sint tag=@ exp=user]
      [%dint tag=@ clu=user exp=user]
  ==
+$  kern
  $~  [%name 0 0]
  $^  [p=kern q=kern]
  $%  [%name dex=@ how=$@(@ [rec=@ arm=@])]
      [%frag axe=@ of=kern]
      [%edit axe=@ tgt=kern val=kern]
      [%litn val=*]
      [%deep val=kern]
      [%bump atm=kern]
      [%same a=kern b=kern]
      [%cond t=kern y=kern n=kern]
      [%peer at=kern in=kern]
      [%letn val=kern in=kern]
      [%rlet rec=kern in=kern]
      [%lamb bod=kern]
      [%appl lam=kern arg=kern]
      [%delt bod=kern]
      [%nock fol=kern arg=kern]
      [%core bat=kern]
      [%pull axe=@ cor=kern]
      [%sint tag=@ exp=kern]
      [%dint tag=@ clu=kern exp=kern]
  ==
--
|%
++  boof
  |*  [g=(each) f=$-(* (each))]
  ?-  -.g
    %&  (f p.g)
    %|  g
  ==
++  lsdectape
  |=  in=tape
  =|  out=@
  =/  plc=@  1
  |-  ^-  @
  ?~  in  out
  %=  $
    in   t.in
    plc  (mul 10 plc)
    out  (add out (mul plc (sub i.in '0')))
  ==
++  nok-fin
  |=  [st=noke-state out=(list noken)]
  ^+  out
  ?@  st  out
  ?+  -.st  ~|(%nok-fin !!)  ::  program bug
    %sym  [[[%sym (crip (flop pen.st))] beg.st] out]
    %num  [[[%num (lsdectape pen.st)] beg.st] out]
  ==
++  print-noke-err
  |=  e=noke-err
  ~&  e
  ^-  tape
  "unexpected {<chr.e>} at line {<lin.loc.e>} col {<col.loc.e>}."
++  nokenize
  |=  in=tape
  =/  [loc=sloc st=noke-state out=(list noken)]
    [[1 1] ~ ~]
  |-  ^-  (each _out noke-err)
  ?~  in  &+(flop (nok-fin st out))
  =+  [c at]=[i.in loc]
  =>  %=  .
        in   t.in
        loc  ?:  =(10 c)
               [+(lin.loc) 1]
             [lin.loc +(col.loc)]
      ==
  ::
  ::  string escapes
  ::
  ?:  ?=([%tae *] st)
    $(st [%tap beg.st c pen.st])
  ?:  ?=([%coe *] st)
    $(st [%cor beg.st c pen.st])
  ::
  ::  inside string literals
  ::
  ?:  ?=([%tap *] st)
    ?:  =('\\' c)
      $(-.st %tae)
    ?:  =('"' c)
      $(out [[[%tap (flop pen.st)] at] out], st ~)
    $(pen.st [c pen.st])
  ?:  ?=([%cor *] st)
    ?:  =('\\' c)
      $(-.st %coe)
    ?:  =('\'' c)
      $(out [[[%cor (crip (flop pen.st))] at] out], st ~)
    $(pen.st [c pen.st])
  ::
  ::  normal char-at-a-time handling
  ::
  ?:  =('\'' c)
    $(st [%cor at ~])
  ?:  =('"' c)
    $(st [%tap at ~])
  ?:  =('(' c)
    $(out [[%'(' at] (nok-fin st out)], st ~)
  ?:  =(')' c)
    $(out [[%')' at] (nok-fin st out)], st ~)
  ?:  =('[' c)
    $(out [[%'[' at] (nok-fin st out)], st ~)
  ?:  =(']' c)
    $(out [[%']' at] (nok-fin st out)], st ~)
  ?:  =('_' c)
    $(out [[[%sym %$] at] (nok-fin st out)], st ~)
  ?:  |(=(' ' c) =(10 c))
    $(out (nok-fin st out), st ~)
  ?:  &((gte c 'a') (lte c 'z'))
    ?@  st  $(st [%sym at c ~])
    ?.  ?=(%sym -.st)  |+[c loc]
    $(pen.st [c pen.st])
  ?:  &((gte c '0') (lte c '9'))
    ?@  st  $(st [%num at c ~])
    ?.  ?=(%num -.st)  |+[c loc]
    $(pen.st [c pen.st])
  |+[c loc]
++  tok-fin
  |=  [st=toke-state out=(list token)]
  ^+  out
  ?@  st  out
  ?+  -.st  ~|(%bad-fin !!)
    %sym  [[%sym (crip (flop +.st))] out]
    %num  [[%num (lsdectape +.st)] out]
  ==
++  tokenize
  |=  in=tape
  =|  [i=@ st=toke-state out=(list token)]
  |-  ^+  out
  ?~  in  (flop (tok-fin st out))
  =+  [c at]=[i.in i]
  =>  .(in t.in, i +(i))
  ?:  ?=([%tae *] st)
    $(st [%tap c +.st])
  ?:  ?=([%coe *] st)
    $(st [%cor c +.st])
  ?:  ?=([%tap *] st)
    ?:  =('\\' c)
      $(-.st %tae)
    ?:  =('"' c)
      $(out [tap+(flop +.st) out], st ~)
    $(+.st [c +.st])
  ?:  ?=([%cor *] st)
    ?:  =('\\' c)
      $(-.st %coe)
    ?:  =('\'' c)
      $(out [cor+(crip (flop +.st)) out], st ~)
    $(+.st [c +.st])
  ?:  =('\'' c)
    $(st [%cor ~])
  ?:  =('"' c)
    $(st [%tap ~])
  ?:  =('(' c)
    $(out [%'(' (tok-fin st out)], st ~)
  ?:  =(')' c)
    $(out [%')' (tok-fin st out)], st ~)
  ?:  =('[' c)
    $(out [%'[' (tok-fin st out)], st ~)
  ?:  =(']' c)
    $(out [%']' (tok-fin st out)], st ~)
  ?:  =('_' c)
    $(out [[%sym %$] (tok-fin st out)], st ~)
  ?:  |(=(' ' c) =('\0a' c))
    $(out (tok-fin st out), st ~)
  ?:  &((gte c 'a') (lte c 'z'))
    ?@  st  $(st [%sym c ~])
    ?>  ?=(%sym -.st)
    $(st [%sym c +.st])
  ?:  &((gte c '0') (lte c '9'))
    ?@  st  $(st [%num c ~])
    ?>  ?=(%num -.st)
    $(st [%num c +.st])
  ~|("unexpected character '{<c>}' at char {<i>}." !!)
++  read
  |=  in=tape
  (read-tokens (tokenize in))
++  read-nokens
  |=  in=(list noken)
  =/  stk=(lest [tag=?(%top %rond %sqar) beg=sloc kid=(list nexp)])
    ~[top+[[0 0] ~]]
  |-  ^-  (each nexp read-nokens-err)
  ?~  in
    ::  stack should have one item in it, or we left out a )]
    ?.  ?=(~ t.stk)
      :-  %|
      ?-  tag.i.stk
        %top   ~|(%read-nokens-bug !!)
        %rond  pope+beg.i.stk
        %sqar  bope+beg.i.stk
      ==
    ?~  kid.i.stk          |+%none
    ?.  ?=(~ t.kid.i.stk)  |+%many
    &+i.kid.i.stk
  =/  t  i.in
  =>  .(in t.in)
  ?-  tok.t
      %'('
    $(stk [rond+[loc.t ~] stk])
      %'['
    $(stk [sqar+[loc.t ~] stk])
      [%sym *]
    $(kid.i.stk [[[%sym +.tok.t] loc.t] kid.i.stk])
      [%num *]
    $(kid.i.stk [[+.tok.t loc.t] kid.i.stk])
      [%cor *]
    $(kid.i.stk [[+.tok.t loc.t] kid.i.stk])
      [%tap *]
    $(kid.i.stk [[[%tape +.tok.t] loc.t] kid.i.stk])
      %')'
    ?-  tag.i.stk
        %top   |+clop+loc.t
        %sqar  |+cbwp+[beg.i.stk loc.t]
        %rond
      ?<  ?=(~ t.stk)  ::  would be %top
      $(stk t.stk(kid.i [[rond+(flop kid.i.stk) beg.i.stk] kid.i.t.stk]))
    ==
      %']'
    ?-  tag.i.stk
        %top   |+clob+loc.t
        %rond  |+cpwb+[beg.i.stk loc.t]
        %sqar
      ?<  ?=(~ t.stk)  ::  would be %top
      $(stk t.stk(kid.i [[sqar+(flop kid.i.stk) beg.i.stk] kid.i.t.stk]))
    ==
  ==
++  read-tokens
  |=  in=(list token)
  =/  stk=(lest (pair ?(%top %rond %sqar) (list sexp)))  ~[top+~]
  |-  ^-  sexp
  ?~  in
    ::  stack should have one item in it, or we left out a )]
    ?.  ?=(~ t.stk)      ~|('unclosed group' !!)
    ?~  q.i.stk          ~|('no expression' !!)
    ?.  ?=(~ t.q.i.stk)  ~|('too many expressions' !!)
    i.q.i.stk
  =/  t  i.in
  =>  .(in t.in)
  ?-  t
      %'('
    $(stk [rond+~ stk])
      %'['
    $(stk [sqar+~ stk])
      [%sym *]
    $(q.i.stk [[%sym +.t] q.i.stk])
      [%num *]
    $(q.i.stk [+.t q.i.stk])
      [%cor *]
    $(q.i.stk [+.t q.i.stk])
      [%tap *]
    $(q.i.stk [[%tape +.t] q.i.stk])
      %')'
    ?-  p.i.stk
        %top   ~|('unmatched closing paren' !!)
        %sqar  ~|('closing bracket with paren' !!)
        %rond
      ?<  ?=(~ t.stk)  ::  would be %top
      $(stk t.stk(q.i [rond+(flop q.i.stk) q.i.t.stk]))
    ==
      %']'
    ?-  p.i.stk
        %top   ~|('unmatched closing bracket' !!)
        %rond  ~|('closing paren with bracket' !!)
        %sqar
      ?<  ?=(~ t.stk)  ::  would be %top
      $(stk t.stk(q.i [sqar+(flop q.i.stk) q.i.t.stk]))
    ==
  ==
++  ntram-sqar
  |=  [l=(list nexp) loc=sloc]
  ^-  (each [tram tram] parse-err)
  ?~  l    |+empty-tram+loc
  ?~  t.l  |+single-tram+loc
  %+  boof  (nparse-tram i.l)  |=  hed=tram
  =/  l=(lest nexp)  t.l
  =-  (boof - |=(tal=tram &+[hed tal]))
  |-  ^-  (each tram parse-err)
  %+  boof  (nparse-tram i.l)  |=  one=tram
  ^-  (each tram parse-err)
  ?~  t.l  &+one
  %+  boof  ^$(l t.l)  |=  mor=tram
  &+[%$ one mor]
++  nparse-tram
  |=  e=nexp
  ^-  (each tram parse-err)
  ?+  exp.e  |+bad-tram+loc.e
      [%sym *]
    [%& +.exp.e]
      [%sqar *]
    (boof (ntram-sqar +.exp.e loc.e) |=([tram tram] &+[%$ +<]))
      [%rond [[%sym @] *] * *]
    %+  boof
      =*  mor  t.exp.e
      ?~  t.mor  :: one more thing, must be sqar
        ?.  ?=([%sqar *] exp.i.mor)  |+bad-tram+loc.i.mor
        (ntram-sqar +.exp.i.mor loc.i.mor)
      (ntram-sqar mor loc.i.mor)  ::  "insert" square
    |=(cel=[tram tram] &+[+.exp.i.+.exp.e cel])
  ==
++  tram-sqar
  |=  l=(list sexp)
  ^-  (unit [tram tram])
  ?~  l    ~
  ?~  t.l  ~
  =/  hed  (parse-tram i.l)
  ?~  hed  ~
  =/  l=(lest sexp)  t.l
  =-  ?~  -  ~
      `[u.hed u]
  |-  ^-  (unit tram)
  =/  one  (parse-tram i.l)
  ?~  one  ~
  ?~  t.l  one
  =/  mor  $(l t.l)
  ?~  mor  ~
  `[%$ u.one u.mor]
++  parse-tram
  |=  e=sexp
  ^-  (unit tram)
  ?+  e  ~
      [%sym *]
    `+.e
      [%sqar *]
    =/  sq  (tram-sqar +.e)
    ?~  sq  ~
    `[%$ u.sq]
      [%rond [%sym @] * *]
    =/  cel=(unit [tram tram])
      =*  mor  t.e
      ?~  t.mor  :: if there's only one more thing, must be square
        ?.  ?=([%sqar *] i.mor)  ~
        (tram-sqar +.i.mor)
      (tram-sqar mor)  :: "insert" square
    ?~  cel  ~
    `[+.i.+.e u.cel]
  ==
++  parse-raph
  |=  e=sexp
  ^-  (unit raph)
  ?+  e  ~
      [%rond [%sym *] * ~]
    `[~ +<+.e (parse-user +>-.e)]
      [%sqar * * *]
    =/  top  $(e +<.e)
    ?~  top  ~
    =/  mor  t.+.e
    =-  ?~(- ~ `[u.top u])
    |-  ^-  (unit raph)
    =/  hed  ^$(e i.mor)
    ?~  hed  ~
    ?~  t.mor  hed
    =/  tal  $(mor t.mor)
    ?~  tal  ~
    `[u.hed u.tal]
  ==
++  june
  |=  [a=user b=user]
  ^-  user
  ?.  &(?=([%litn *] a) ?=([%litn *] b))
    [%cons a b]
  [%litn val.a val.b]
++  massage-args
  |=  arg=(list sexp)
  ^-  sexp
  ?~  arg  ~|('empty argument list' !!)
  ?~  t.arg  i.arg
  [%sqar arg]
++  parse-prog
  |=  e=sexp
  ^-  prog
  ?.  ?=([%rond [%sym %main] *] e)
    [%$ (parse-user e)]
  =*  l  +.e
  ?>  =(3 (lent l))
  :-  (need (parse-tram &2.l))
  (parse-user &3.l)
++  parse-user
  |=  e=sexp
  ^-  user
  ?@  e  litn+e
  ?-  -.e
      %sym
    +.e
      %tape
    [%litn +.e]
      %sqar
    =*  l  +.e
    ?~  l  ~|('empty brackets' !!)
    ?~  t.l  ~|('singleton brackets' !!)
    %+  june  $(e i.l)
    =/  p=(lest sexp)  t.l
    |-  ^-  user
    =/  one  ^$(e i.p)
    ?~  t.p  one
    (june one $(p t.p))
      %rond
    =*  l  +.e
    =/  op  &1.l
    ?.  ?=([%sym *] op)
      ?>  (gth (lent l) 1)
      [%appl $(e op) $(e (massage-args +.l))]
    ?+  +.op  ~|  l
              ?>  (gth (lent l) 1)
              [%appl +.op $(e (massage-args +.l))]
        %frag
      ?>  =(3 (lent l))
      =/  axe  &2.l
      ?>  ?=(@ axe)
      [%frag axe $(e &3.l)]
        %edit
      ?>  =(4 (lent l))
      =/  axe  &2.l
      ?>  ?=(@ axe)
      [%edit axe $(e &3.l) $(e &4.l)]
        %bump
      ?>  =(2 (lent l))
      [%bump $(e &2.l)]
        %deep
      ?>  =(2 (lent l))
      [%deep $(e &2.l)]
        %same
      ?>  =(3 (lent l))
      [%same $(e &2.l) $(e &3.l)]
        %if
      ?>  =(4 (lent l))
      [%cond $(e &2.l) $(e &3.l) $(e &4.l)]
        %focus
      ?>  =(4 (lent l))
      [%peer (need (parse-tram &2.l)) $(e &3.l) $(e &4.l)]
        %let
      ?>  =(4 (lent l))
      =/  nam  &2.l
      [%letn (need (parse-tram nam)) $(e &3.l) $(e &4.l)]
        %rlet
      ?>  =(3 (lent l))
      [%rlet (need (parse-raph &2.l)) $(e &3.l)]
        %nock
      ?>  =(3 (lent l))
      [%nock $(e &2.l) $(e &3.l)]
        %fn
      =/  len  (lent l)
      ?+  len  ~|("fn has {<len>} args" !!)
        %3  [%lamb (need (parse-tram &2.l)) $(e &3.l)]
        %4  =/  nex  &2.l
            ?>  ?=([%sym *] nex)
            [%recl +.nex (need (parse-tram &3.l)) $(e &4.l)]
      ==
        %dfn
      ?>  =(3 (lent l))
      =/  arg  &2.l
      [%delt (need (parse-tram arg)) $(e &3.l)]
        %core
      =/  arg
        ?:  =(2 (lent l))
          &2.l
        [%sqar +.l]
      [%core (need (parse-raph arg))]
        %pull
      ?>  =(3 (lent l))
      =/  axe=sexp  &2.l
      ?>  ?=(@ axe)
      [%pull axe $(e &3.l)]
        %sint
      ?>  =(3 (lent l))
      =/  tag  &2.l
      ?>  ?=(@ tag)
      [%sint tag $(e &3.l)]
        %dint
      ?>  =(4 (lent l))
      =/  tag  &2.l
      ?>  ?=(@ tag)
      [%dint tag $(e &3.l) $(e &4.l)]
    ==
  ==
++  bond-delv
  =/  axe=@  1
  |=  [b=bond n=@t]
  ^-  fund
  ?-  b
      @
    ?.  =(n b)  ~
    leg+axe
      [%cell *]
    ?:  =(n n.b)  leg+axe
    =/  l  $(b l.b, axe (peg axe 2))
    ?.  ?=(~ l)  l
    $(b r.b, axe (peg axe 3))
      [%core *]
    =/  fib=fund  :: found in battery
      =/  arm=@  2
      =/  bat=neet  bat.b
      |-  ^-  fund
      ?@  bat  ?:(=(n bat) [%arm axe arm] ~)
      =/  l  $(arm (peg 2 arm), bat p.bat)
      ?.  ?=(~ l)  l
      $(arm (peg arm 3), bat q.bat)
    ?.  ?=(~ fib)  fib
    $(b pay.b, axe (peg axe 3))
  ==
++  gamma-find
  =|  del=@
  |=  [g=gamma n=@t]
  ^-  path
  =/  u=fund   (bond-delv i.g n)
  ?.  ?=(~ u)  [del u]
  ?~  t.g    ~
  $(g t.g, del +(del))
++  tram-to-bond
  |=  t=tram
  ^-  bond
  ?@  t  t
  [%cell n.t $(t l.t) $(t r.t)]
++  extend-tram
  |=  [g=gamma t=tram]
  ^-  gamma
  [[%cell %$ (tram-to-bond t) i.g] t.g]
++  prog-to-kern
  |=  pog=prog
  (user-to-kern exp.pog [(tram-to-bond arg.pog) ~])
++  user-to-kern
  |=  [e=user g=gamma]
  ::  =-  ~&  [%user exp=e pro=-]  -
  =<  $
  |% 
  ++  core
    |=  rap=raph
    ^-  [kern gamma]
    =+  |-  ^-  [n=neet u=user]
        ?~  -.rap  +.rap
        =/  l  $(rap p.rap)
        =/  r  $(rap q.rap)
        [[n.l n.r] %cons u.l u.r]
    =.  g  [[%core n i.g] t.g]
    [^$(e u) g]
  ++  $
    ^-  kern
    ?@  e
      ?~  e  ~|("empty symbol (_) in variable position" !!)
      =/  p=path  (gamma-find g e)
      ?~  p  ~|("unbound name {<e>}" !!)
      [%name del.p +>.p]
    ?-  -.e
      %cons  [$(e p.e) $(e q.e)]
      %frag  [%frag axe.e $(e of.e)]
      %edit  [%edit axe.e $(e tgt.e) $(e val.e)]
      %litn  e
      %bump  [%bump $(e atm.e)]
      %deep  [%deep $(e val.e)]
      %same  [%same $(e a.e) $(e b.e)]
      %cond  [%cond $(e t.e) $(e y.e) $(e n.e)]
      %peer  =/  at  $(e at.e)
             [%peer at $(e in.e, i.g (tram-to-bond nam.e))]
      %letn  [%letn $(e val.e) $(e in.e, g (extend-tram g nam.e))]
      %rlet  =^  k  g  (core g.e)
             [%rlet k $(e in.e)]  
      %lamb  [%lamb $(e bod.e, g (extend-tram g arg.e))]
      %recl  $(e [%rlet [~ nam.e %lamb arg.e bod.e] nam.e])
      %appl  [%appl $(e lam.e) $(e arg.e)]
      %delt  [%delt $(e bod.e, g [(tram-to-bond arg.e) g])]
      %nock  [%nock $(e fol.e) $(e arg.e)]
      %core  [%core -:(core g.e)]
      %pull  [%pull axe.e $(e cor.e)]
      %sint  [%sint tag.e $(e exp.e)]
      %dint  [%dint tag.e $(e clu.e) $(e exp.e)]
    ==
  --
++  unq
  |=  [dex=@ axe=@]
  =/  f=*  [0 axe]
  ?~  dex  f
  :-  1
  =|  i=@
  |-  ^-  *
  ?:  =(i dex)  f
  $(i +(i), f [',' f])
++  kern-to-punk
  |=  e=kern
  ::  =-  ~&  [%kern exp=e pro=-]  -
  ^-  *  ::  punk
  ?-  -.e
    ^      [$(e p.e) $(e q.e)]
    %name  ?@  how.e  (unq dex.e how.e)
           [9 ['\'' arm.how.e] (unq dex.e rec.how.e)]
    %frag  [7 $(e of.e) 0 axe.e]
    ::  whenever input can determine the head of a cell,
    ::  like the axis of our edit here, we must hard quote it
    ::  to prevent punk from seeing it as an operator
    %edit  [10 [['\'' axe.e] $(e val.e)] $(e tgt.e)]
    %litn  [1 '\'' val.e]
    %deep  [3 $(e val.e)]
    %bump  [4 $(e atm.e)]
    %same  [5 $(e a.e) $(e b.e)]
    %cond  [6 $(e t.e) $(e y.e) $(e n.e)]
    %peer  [7 $(e at.e) $(e in.e)]
    %letn  [8 $(e val.e) $(e in.e)]
    %rlet  [8 [1 $(e rec.e)] $(e in.e)]
    %lamb  [[1 $(e bod.e)] 0 1]
    %appl  [7 [$(e lam.e) $(e arg.e)] 2 [[0 3] 0 5] 0 4]
    %delt  ['`' $(e bod.e)]
    %nock  [2 $(e arg.e) $(e fol.e)]
    %core  [[1 $(e bat.e)] 0 1]
    %pull  [9 ['\'' axe.e] $(e cor.e)]
    %sint  [11 ['\'' tag.e] $(e exp.e)]
    %dint  [11 [['\'' tag.e] $(e clu.e)] $(e exp.e)]
  ==
++  prog-to-nock
  |=  pog=prog
  %-  compile:punk
  %-  kern-to-punk
  %-  prog-to-kern
  pog
++  tape-to-prog
  |=  t=tape
  %-  parse-prog
  %-  read
  t
++  compile-tape
  |=  t=tape
  %-  prog-to-nock
  %-  tape-to-prog
  t
++  run-tape
  |=  t=tape
  .*  ~  (compile-tape t)
++  cram
  |=  v=vase
  ~(ram re (sell v))
++  run-slog
  |=  t=tape
  =/  pog=prog  (tape-to-prog t)
  ~&  prog=(cram !>(pog))
  =/  n=*  (prog-to-nock pog)
  ~&  nock=(cram !>(n))
  .*(~ n)
--
=/  cmd
  $@  %test
  $%  [%read tape]
      [%eval tape]
      [%load path]
  ==
:-  %say
|=  [^ [=cmd ~] ~]
:-  %noun
?-  cmd
    [%read *]
  (read +.cmd)
    [%eval *]
  (run-tape +.cmd)
    [%load *]
  =/  w=wain  .^(wain %cx +.cmd)
  =/  c=cord  (of-wain:format w)
  =/  t=tape  (trip c)
  (run-tape t)
    %test
  ~|  t+'raph parse'
  ?>  .=  `[~ %x %litn 12]  (parse-raph (read "(x 12)"))
  ?>  .=  `[[~ %x %litn 40] ~ %y %litn 2]
      (parse-raph (read "[(x 40) (y 2)]"))
  ~|  t+0
  ?>  .=  42
      .*  ~  (prog-to-nock %$ %appl [%lamb %a %a] %litn 42)
  ~|  t+1
  ?>  .=  42
      (lsdectape "24")
  ~|  t+2
  ?>  .=  [42 63]  :: dfns can close over lexicals
      .*  63
      (run-tape "(let x 42 (dfn y [x y]))")
  ~|  t+3
  ?>  .=  [42 63]  :: dfns can close over dexicals
      %-  run-tape
      "(nock (nock (dfn x (dfn y [x y])) 42) 63)"
  ~|  t+"literal nock formula"
  ?>  .=  42
      %-  run-tape
      "(nock [4 0 1] 41)"
  ~|  t+'read'
  ?>  .=  [%rond 1 2 3 ~]          (read "(1 2 3)")
  ?>  .=  [%sqar 1 2 3 ~]          (read "[1 2 3]")
  ?>  .=  [%sqar 1 [%rond ~] 3 ~]  (read "[1 () 3]")
  ~|  t+'tram parse'
  =/  ptr  |=(a=tape (parse-tram (read a)))
  ?>  .=  `%x
      (ptr "x")
  ?>  .=  `[%$ %x %y]
      (ptr "[x y]")
  ?>  .=  `[%$ %x %$ %y %z]
      (ptr "[x y z]")
  ?>  .=  `[%$ [%$ %x %y] %z]
      (ptr "[[x y] z]")
  ?>  .=  `[%foo [%bar %x %y] %z]
      (ptr "(foo [(bar [x y]) z])")
  ?>  =(~ (ptr "(foo x)"))
  ?>  =(~ (ptr "(foo (bar [x y]))"))
  ~|  t+%fst
  ?>  .=  40       (run-tape "((fn [x y] x) [40 2])")
  ?>  .=  40       (run-tape "((fn [x _] x) [40 2])")
  ~|  t+%snd
  ?>  .=  2        (run-tape "((fn [x y] y) [40 2])")
  ?>  .=  2        (run-tape "((fn [_ y] y) [40 2])")
  ~|  t+%focus
  ::  i would have to mink to test erasure of bindings because
  ::  compiler crashes on unbound variables
  ::  so we just test that it compiles to 7 :)
  ?>  .=  [7 [1 42] 0 1]  (compile-tape "(focus a 42 a)")
  ~|  t+'destructuring let'
  ?>  .=  5        (run-tape "(let [x y z] [3 4 5] z)")
  ?>  .=   [3 4 5 [4 5] 3 4 5]
      %-  run-tape
      "(let (foo [x (bar [y z])]) [3 4 5] [x y z bar foo])"
  ?>  .=   [3 4 5 [4 5] 3 4 5]
      %-  run-tape
      "(let (foo x (bar y z)) [3 4 5] [x y z bar foo])"
  ~|  t+'parallel let'
  ?>  .=  [2 40]   (run-tape "(let [x y] [40 2] [y x])")
  ~|  t+%args
  ::  you may omit the brackets for cell args just like hoon
  ?>  .=  [0 42]
      %-  run-tape
      "((fn x x) 0 42)"
  ~|  t+%lits
  ?>  .=  [40 2]   (run-tape "[40 2]")
  ?>  .=  "hello, world!"  (run-tape "\"hello, world!\"")
  ?>  .=  'hello, world!'  (run-tape "'hello, world!'")
  ?>  .=  "'"  (run-tape "\"'\"")
  ?>  .=  '"'  (run-tape "'\"'")
  ::  punk special characters inside lits must be hard quoted
  ?>  .=  [44 0 1]  (run-tape "[44 0 1]")
  ~|  t+%sqar
  ?>  .=  [1 40 2]
      (compile-tape "[40 2]")
  ?>  .=  [40 2]
      (run-tape "(let x 40 (let y 2 [x y]))")
  ~|  t+%edit
  ?>  .=  [1 42 3]
      (run-tape "(edit 6 [1 2 3] 42)")
  ::  axis ',' (44) tests a corner of punk
  ::  so first make sure its sibling works
  ?>  .=  [[1 2 [[3 4] 5]] 6]
      .*  [[1 2 [[3 13] 5]] 6]
      (run-tape "(dfn x (edit 45 x 4))")
  ::  now if we haven't quoted edit properly, this will fail
  ?>  .=  [[1 2 [[3 4] 5]] 6]
      .*  [[1 2 [[13 4] 5]] 6]
      (run-tape "(dfn x (edit 44 x 3))")
  ::  XX we should have a test for pulling axis 44, but don't yet
  ~|  t+%hints
  ?>  .=  42  (run-tape "(sint 44 42)")
  ?>  .=  42  (run-tape "(dint 44 0 42)")
  ~|  t+%id
  ?>  .=  42       (run-tape "((fn x x) 42)")
  ~|  t+%nest
  ?>  .=  [40 2]   (run-tape "(((fn x (fn y [x y])) 40) 2)")
  ~|  t+%pull
  ?>  .=  42  .*  |.(42)
      %-  run-tape
      "(dfn trap (pull 2 trap))"
  ?>  .=  [40 2]  %-  run-tape
      "(let c (core [(_ 40) (_ 2)]) [(pull 4 c) (pull 5 c)])"
  ?>  .=  [40 2]  %-  run-tape
      ::  you can leave the outer [] off the shape for core
      "(let c (core (_ 40) (_ 2)) [(pull 4 c) (pull 5 c)])"
  =/  dec-src=tape
    "(let fix (fn exp (let a (fn f (exp (fn x ((f f) x)))) (a a))) (let dec (fn n ((fix (fn r (fn i (let up (bump i) (if (same up n) i (r up)))))) 0)) (dec 43)))"
  ?.  =(42 (run-tape dec-src))
    ~|([t+%dec (cram !>((compile-tape dec-src)))] !!)
  ~|  t+%rlet
  ?>  =(42 (run-tape "(rlet (x 42) x)"))
  ~|  t+%'hold your breath, make a wish...'
  ?>  .=  3  %-  run-tape
    "(rlet (loop (fn x (if (same x 3) x (loop (bump x))))) (loop 1))"
  ~|  t+%'count to three, with sugar'
  ?>  .=  3  %-  run-tape
    "((fn loop x (if (same x 3) x (loop (bump x)))) 1)"
  =/  lrdec-src=tape
    "(let dec (fn n (rlet (loop (fn i (let up (bump i) (if (same up n) i (loop up))))) (loop 0))) (dec 43))"
  ?.  =(42 (run-tape lrdec-src))
    ~|([t+%lrdec (cram !>((compile-tape lrdec-src)))] !!)
  ~&  (cram !>((compile-tape lrdec-src)))
  ~|  t+%odd
  =/  ddec  %-  compile-tape
"""
(main n
 ((fn loop i
   (let up (bump i)
    (if (same up n)
     i
     (loop up)))) 0))
"""
  ?>  =(42 .*(43 ddec))
::  this "module" "imports" dec (by taking it as an argument)
::  then it defines two mutually recursive dfns, odd and evn
::  and returns them
  =+  ^=  [odd even]  .*  ddec  %-  compile-tape
"""
(main dec
 (rlet
  [(odd (dfn n (if (same 0 n) 1 (nock evn (nock dec n)))))
   (evn (dfn n (if (same 0 n) 0 (nock odd (nock dec n)))))]
  [odd evn]))
"""
  ?>  =(0 .*(42 even))
  ?>  =(1 .*(42 odd))
  ~|  t+"ffi"
  =/  fact-module  %-  compile-tape
"""
(main [lth mul dec]
 (let slam (fn [cor sam] (pull 2 (edit 6 cor sam)))
  (dfn n
   ((fn fac n
     (if (slam lth n 2)
      1
      (slam mul n (fac (slam dec n)))))
    n))))
"""
  ?>  .=  120
      .*  5
      .*  [lth mul dec]
      fact-module
  =/  nok  (nokenize "[a b c]")
  ?>  ?=(%& -.nok)
  =/  red  (read-nokens p.nok)
  ?>  ?=(%& -.red)
  (nparse-tram p.red)
==
==
