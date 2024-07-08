/-  loon-token
=,  loon-token
=-  ^?
    |%
    ++  tokenize  gen
    ++  pretty-sloc
      |=  loc=sloc
      "line {<lin.loc>} col {<col.loc>}"
    ++  pretty-toke-err
      |=  e=toke-err
      ^-  tape
      "unexpected {<chr.e>} at {(pretty-sloc loc.e)}."
    --
=/  state
  $@  ?(~ %com)
  [?(%sym %tap %tae %cor %coe) beg=sloc pen=tape]
=/  [pre=sloc at=sloc cur=sloc st=state out=(list toke)]
  [[0 0] [1 0] [1 1] ~ ~]
|%
++  lick
  |=  [beg=sloc t=toad]
  +>(st ~, out [[[beg at] t] out])
++  close
  |=  end=sloc
  ^+  out
  ?@  st  out
  :_  out
  ?>  ?=(%sym -.st)
  :-  [beg.st end]
  ?:  =("_" pen.st)  symb+%$  :: empty binder
  =/  [cs=tape plc=@ sum=@]  [pen.st 1 0]
  |-  ^-  toad
  ?~  cs  atom+sum
  =*  c  i.cs
  ?.  &((gte c '0') (lte c '9'))  symb+(crip (flop pen.st))
  %=  $
    cs   t.cs
    plc  (mul 10 plc)
    sum  (add sum (mul plc (sub c '0')))
  ==
++  gen
  |=  in=tape
  ^-  (each (list toke) toke-err)
  ?~  in  &+(flop (close at))
  ::
  ::  read a character c and remember its source location at
  ::
  =/  c  i.in
  =>  %=  .
        in   t.in
        pre  at
        at   cur
        cur  ?:  =(10 c)
               [+(lin.cur) 1]
             [lin.cur +(col.cur)]
      ==
  ::
  ::  inside comments
  ::
  ?:  ?=(%com st)
    ?.  =(10 c)  $
    $(st ~)
  ::
  ::  string escapes
  ::
  ?:  ?=([%tae *] st)
    $(st [%tap beg.st c pen.st])
  ?:  ?=([%coe *] st)
    $(st [%cor beg.st c pen.st])
  ::
  ::  inside of string literals
  ::
  ?:  ?=([%tap *] st)
    ?:  =('\\' c)   
      $(-.st %tae)  :: tape escape mode
    ?:  =('"' c)    :: end of tape
      $(+> (lick beg.st tape+(flop pen.st)))
    $(pen.st [c pen.st])
  ?:  ?=([%cor *] st)
    ?:  =('\\' c)
      $(-.st %coe)  :: cord escape mode
    ?:  =('\'' c)   :: end of cord
      $(+> (lick beg.st cord+(crip (flop pen.st))))
    $(pen.st [c pen.st])
  ::
  ::  normal char-at-a-time handling
  ::
  ?:  =(';' c)  :: begin comment
    $(st %com)
  ?:  =('\'' c)
    $(st [%cor at ~])  :: begin cord
  ?:  =('"' c)
    $(st [%tap at ~])  :: begin tape
  ?:  ?=(?(%'(' %')' %'[' %']') c)
    $(st ~, out [[c at] (close pre)])
  =*  die  |+[c at]
  ::
  ::  whitespace
  ::
  ?:  |(=(' ' c) =(10 c))
    $(st ~, out (close pre))
  ?.  &((gte c '!') (lte c '~'))  die
  ::
  ::  symbols/numbers (a number is a symbol with just numbers)
  ::
  ?@  st  $(st [%sym at c ~])
  $(pen.st [c pen.st])
--
