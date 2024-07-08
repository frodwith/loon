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
=/  lsdectape
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
=/  state
  $@  ?(~ %com)
  [?(%sym %num %tap %tae %cor %coe) beg=sloc pen=tape]
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
  ?+  -.st  ~|(%close !!)  ::  program bug
    %num  [[beg.st end] %atom (lsdectape pen.st)]
    %sym  [[beg.st end] %symb (crip (flop pen.st))]
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
  ?:  =('_' c)         :: empty binder
    ?^  st  die
    $(+> (lick at %symb %$))
  ::
  ::  whitespace
  ::
  ?:  |(=(' ' c) =(10 c))
    $(st ~, out (close pre))
  ::
  ::  letters
  ::
  ?:  &((gte c 'a') (lte c 'z'))
    ?@  st  $(st [%sym at c ~])
    ?.  ?=(%sym -.st)  die
    $(pen.st [c pen.st])
  ::
  ::  digits
  ::
  ?:  &((gte c '0') (lte c '9'))
    ?@  st  $(st [%num at c ~])
    ?.  ?=(%num -.st)  die
    $(pen.st [c pen.st])
  die
--
