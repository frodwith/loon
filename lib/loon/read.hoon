/-  loon-read, tsur=loon-token
/+  tlib=loon-token
=,  tsur
=,  tlib
=,  loon-read
=-  ^-  $:  $=  read
            $-((list toke) (each sexp read-err))
            $=  read-tape
            $-(tape (each sexp (each toke-err read-err)))
            $=  pretty-read-err
            $-(read-err tape)
        ==
    :+  read
      |=  in=tape
      ^-  (each sexp (each toke-err read-err))
      =/  t  (tokenize in)
      ?.  ?=(%& -.t)  |+&+p.t
      =/  r  (read p.t)
      ?.  ?=(%& -.r)  |+|+p.r
      &+p.r
    |=  e=read-err
    ^-  tape
    =*  ps  pretty-sloc
    ?-  e
      %none      "no expressions"
      %many      "too many expressions"
      [%pope *]  "unclosed '(' at {(ps loc.e)}."
      [%bope *]  "unclosed '[' at {(ps loc.e)}."
      [%clop *]  "unmatched ')' at {(ps loc.e)}."
      [%clob *]  "unmatched ']' at {(ps loc.e)}."
      [%cpwb *]  "'(' at {(ps p.e)} closed by ']' at {(ps b.e)}."
      [%cbwp *]  "'[' at {(ps b.e)} closed by ')' at {(ps p.e)}."
    ==
=/  stk=(lest [tag=?(%top %rond %sqar) beg=sloc kid=(list sexp)])
  ~[top+[[0 0] ~]]
^=  read
|=  in=(list toke)
^-  (each sexp read-err)
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
      %symb  t
      %tape  t
      %atom  [ran.t +.dat.t]
      %cord  [ran.t +.dat.t]
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
           :-  [beg.i.stk loc.t]
           rond+(flop kid.i.stk)
  ==  ==  ==
    %']'
  ?-  tag.i.stk
    %top   |+clob+loc.t
    %rond  |+cpwb+[beg.i.stk loc.t]
    %sqar
  ?<  ?=(~ t.stk)  ::  would be %top
  %=  $  stk
  %=  t.stk
    kid.i  :_  kid.i.t.stk
           :-  [beg.i.stk loc.t]
           sqar+(flop kid.i.stk)
  ==  ==  ==
==
