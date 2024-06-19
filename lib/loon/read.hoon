/-  tsur=loon-token, loon-read
/+  tlib=loon-token
=,  tsur
=,  tlib
=,  loon-read
^?
|%
++  cons
  |=  [h=sexp t=sexp]
  [%pair +<]
++  car
  |=  e=sexp
  ?+  e  !!
    ::  it is historically convenient to have (car/cdr nil) -> nil
    [%null *]  e
    [%pair *]  p.e
  ==
++  cdr
  |=  e=sexp
  ?+  e  !!
    [%null *]  e
    [%pair *]  q.e
  ==
++  erase
  |=  e=lexp
  ^-  sexp
  ?@  exp.e  [%atom exp.e]
  ?-  -.exp.e
    %symb  exp.e
    %cord  [%atom +.exp.e]
    %tape  =/  l  +.exp.e
           |-  ^-  sexp
           ?~  l  [%atom ~]
           :-  [%atom i.l]
           $(l t.l)
    %rond  =/  l  +.exp.e
           |-  ^-  sexp
           ?~  l  [%null ~]
           :+  %pair  ^$(e i.l)
           $(l t.l)
    %sqar  :-  $(e i.exp.e)
           =/  mor  t.exp.e
           |-  ^-  sexp
           =/  hed  ^$(e i.mor)
           ?~  t.mor  hed
           [hed $(mor t.mor)]
  ==
++  nullify
  |=  e=sexp
  ^-  $@(~ lexp)  ::  improper lists fail
  ?-  -.e
      %symb
    ::  the ` means null spam
    `e
      %atom
    `a.e
      %null
    `[%rond ~]
      %pair
    =/  hed  $(e p.e)
    ?~  hed  ~
    =/  tal  $(e q.e)
    ::  see? failure.
    ?.  ?=([~ %rond *] tal)  ~
    tal(+.exp [hed +.exp.tal])
      ^
    =/  hed  $(e p.e)
    ?~  hed  ~
    =/  tal  $(e q.e)
    ?~  tal  ~
    ?:  ?=([%sqar *] exp.tal)
      tal(+.exp [hed +.exp.tal])
    `sqar+~[hed tal]
  ==
++  read
  =/  stk=(lest [tag=?(%top %rond %sqar) beg=sloc kid=(list lexp)])
    ~[top+[[0 0] ~]]
  |=  [id=path in=(list toke)]
  ^-  (each lexp read-err)
  ?~  in
    ::  stack should have one item in it, or we left out a )]
    ?.  ?=(~ t.stk)
      :-  %|
      ?-  tag.i.stk
        %top   ~|(%read-bug !!)
        %rond  pope+beg.i.stk
        %sqar  bope+beg.i.stk
      ==
    ?~  kid.i.stk          |+%none
    ?.  ?=(~ t.kid.i.stk)  |+%many
    &+i.kid.i.stk
  =/  t  i.in
  =>  .(in t.in)
  ?^  -.t
    %=  $  kid.i.stk  :_  kid.i.stk
      ?-  -.dat.t
        %symb  [[id ran.t] dat.t]
        %tape  [[id ran.t] dat.t]
        %atom  [[id ran.t] +.dat.t]
        %cord  [[id ran.t] +.dat.t]
      ==
    ==
  ?-  c.t
      %'('
    $(stk [rond+[loc.t ~] stk])
      %'['
    $(stk [sqar+[loc.t ~] stk])
      %')'
    ?-  tag.i.stk
      %top   |+clop+loc.t
      %sqar  |+cbwp+[beg.i.stk loc.t]
      %rond
        ?<  ?=(~ t.stk)  ::  would be %top
        %=  $  stk
        %=  t.stk
          kid.i  :_  kid.i.t.stk
                 :-  [id beg.i.stk loc.t]
                 rond+(flop kid.i.stk)
    ==  ==  ==
      %']'
    ?-  tag.i.stk
      %top   |+clob+loc.t
      %rond  |+cpwb+[beg.i.stk loc.t]
      %sqar
        ?<  ?=(~ t.stk)  ::  would be %top
        =/  ran    [beg.i.stk loc.t]
        =/  bak    (flop kid.i.stk)
        ?~  bak    |+[%bnum %0 ran]
        ?~  t.bak  |+[%bnum %1 ran]
        $(stk t.stk(kid.i [[[id ran] sqar+bak] kid.i.t.stk]))
    ==
  ==
++  read-tape
  |=  [id=path t=tape]
  ^-  (each lexp read-tape-err)
  =/  tok  (tokenize t)
  ?.  ?=(%& -.tok)  |+&+p.tok
  =/  red  (read id p.tok)
  ?.  ?=(%& -.red)  |+|+p.red
  &+p.red
++  pretty-read-err
  |=  e=read-err
  ^-  tape
  =*  ps  pretty-sloc
  ?-  e
    %none      "no expressions"
    %many      "too many expressions"
    [%pope *]  "unclosed '(' at {(ps loc.e)}."
    [%bope *]  "unclosed '[' at {(ps loc.e)}."
    [%bnum *]  =/  complaint=tape
                 ?-  n.e
                   %0  "are empty"
                   %1  "contain only one item"
                 ==
    "brackets beginning at {(ps beg.e)} and ending at {(ps end.e)} {complaint}."
    [%clop *]  "unmatched ')' at {(ps loc.e)}."
    [%clob *]  "unmatched ']' at {(ps loc.e)}."
    [%cpwb *]  "'(' at {(ps p.e)} closed by ']' at {(ps b.e)}."
    [%cbwp *]  "'[' at {(ps b.e)} closed by ')' at {(ps p.e)}."
  ==
++  pretty-read-tape-err
  |=  e=read-tape-err
  ?:  ?=(%& -.e)  (pretty-toke-err p.e)
  (pretty-read-err p.e)
--
