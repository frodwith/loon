/+  punk
=~
::  the lambda-delta calculus is an augmentation of the untyped lambda calculus.
::  we start with abstraction and application (lamb/appl), and we add:
::    nouns (cons,1,3,4,5,10)
::    let (8 - the subject is a list of bound values)
::    if-then-else (6)
::    hints (11)
::    delta abstraction and application (quasiquotes lambdas, delt/appd)
::  we compile to nock through punk, the quasiquote-nock.
|%
+$  token :: XX: add position info
  $@  ?(%'(' %')')
  $%  [%sym @t]
      [%num @]
  ==
+$  sexp
  $@  @
  $%  [%sym @t]
      [%list (list sexp)]
  ==
+$  toke-state
  $@  ~
  [?(%sym %num) (list @t)]
+$  user
  $~  %a
  $@  @t
  $%  [%cons p=user q=user]
      [%frag axe=@ of=user]
      [%edit axe=@ tgt=user val=user]
      [%quot val=*]
      [%bump atm=user]
      [%deep val=user]
      [%same a=user b=user]
      [%cond t=user y=user n=user]
      [%letn nam=@t val=user in=user]
      [%lamb arg=@t bod=user]
      [%appl lam=user arg=user]
      [%delt arg=@t bod=user]
      [%appd del=user arg=user]
      [%sint tag=@ exp=user]
      [%dint tag=@ clu=user exp=user]
  ==
+$  core
  $~  [%name 0 0]
  $^  [p=core q=core]
  $%  [%name dex=@ lex=@]
      [%frag axe=@ of=core]
      [%edit axe=@ tgt=core val=core]
      [%quot val=*]
      [%deep val=core]
      [%bump atm=core]
      [%same a=core b=core]
      [%cond t=core y=core n=core]
      [%letn val=core in=core]
      [%lamb bod=core]
      [%appl lam=core arg=core]
      [%delt bod=core]
      [%appd del=core arg=core]
      [%sint tag=@ exp=core]
      [%dint tag=@ clu=core exp=core]
  ==
+$  bind
  [del=@ lam=@]
+$  env
  (map @t bind)
--
|%
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
++  tok-fin
  |=  [st=toke-state out=(list token)]
  ^+  out
  ?@  st  out
  ?-  -.st
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
  ?:  =('(' c)
    $(out [%'(' (tok-fin st out)], st ~)
  ?:  =(')' c)
    $(out [%')' (tok-fin st out)], st ~)
  ?:  =(' ' c)
    $(out (tok-fin st out), st ~)
  ?:  &((gte c 'a') (lte c 'z'))
    ?@  st  $(st [%sym c ~])
    ?-  -.st
      %sym  $(st [%sym c +.st])
      %num  ~|("unexpected letter '{<c>}' at char {<i>}." !!)
    ==
  ?:  &((gte c '0') (lte c '9'))
    ?@  st  $(st [%num c ~])
    ?-  -.st
      %sym  ~|("unexpected digit '{<c>}' at char {<i>}." !!)
      %num  $(st [%num c +.st])
    ==
  ~|("unexpected character '{<c>}' at char {<i>}." !!)
++  read
  |=  in=(list token)
  =|  stk=(lest (list sexp))
  |-  ^-  sexp
  ?~  in
    ?~  t.stk
      ?~  i.stk  ~|(%a !!)  :: XX - error messages
      ?~  i.i.stk  ~|(%b !!)
      i.i.stk
    ~|(%c !!)
  =/  t  i.in
  =>  .(in t.in)
  ?-  t
    %'('      $(stk [~ stk])
    %')'      ?~  t.stk  !!
              $(stk [[[%list (flop i.stk)] i.t.stk] t.t.stk])
    [%sym *]  $(stk [[[%sym +.t] i.stk] t.stk])
    [%num *]  $(stk [[+.t i.stk] t.stk])
  ==
++  parse
  |=  e=sexp
  ^-  user
  ?@  e  quot+e
  ?-  -.e
    %sym  +.e
    %list
    =*  l  +.e
    =/  op  &1.l
    ?.  ?=([%sym *] op)
      ?>  =(2 (lent l))
      [%appl $(e op) $(e &2.l)]
    ?+  +.op  ~|  l
              ?>  =(2 (lent l))
              [%appl +.op $(e &2.l)]
        %cons
      ?>  =(3 (lent l))
      [%cons $(e &2.l) $(e &3.l)]
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
        %quote
      :-  %quot
      =*  n  +.l
      ?@  n  n
      ?>  ?=(%list -.n)
      =*  m  +.n
      ?<  ?=(~ m)
      ?<  ?=(~ +.m)
      =/  o=(lest sexp)  m
      |-  ^-  *
      ?~  t.o  i.o
      [i.o $(o t.o)]
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
        %let
      ?>  =(4 (lent l))
      =/  nam  &2.l
      ?>  ?=([%sym *] nam)
      [%letn +.nam $(e &3.l) $(e &4.l)]
        %dcall
      ?>  =(3 (lent l))
      [%appd $(e &2.l) $(e &3.l)]
        %fn
      ?>  =(3 (lent l))
      =/  arg  &2.l
      ?>  ?=([%sym *] arg)
      [%lamb +.arg $(e &3.l)]
        %dfn
      ?>  =(3 (lent l))
      =/  arg  &2.l
      ?>  ?=([%sym *] arg)
      [%delt +.arg $(e &3.l)]
        %sint
      ?>  =(3 (lent l))
      =/  tag  &2.l
      ?>  ?=(@ tag)
      [%sint +.tag $(e &3.l)]
        %dint
      ?>  =(4 (lent l))
      =/  tag  &2.l
      ?>  ?=(@ tag)
      [%dint +.tag $(e &3.l) $(e &4.l)]
    ==
  ==
++  bind-del
  |=  [nam=@ =env]
  %.  [nam 0 0]
  %~  put  by
  %-  ~(run by env)
  |=  a=bind
  a(del +(del.a))
++  bind-lam
  |=  [nam=@ =env]
  %.  [nam 0 1]
  %~  put  by
  %-  ~(run by env)
  |=  a=bind
  ?.  =(0 del.a)  a
  ?:  =(0 lam.a)  a
  a(lam +(lam.a))
++  user-to-core
  |=  e=user
  ::  =-  ~&  [%user exp=e pro=-]  -
  =|  =env
  |-  ^-  core
  ?@  e
    name+(~(got by env) e)
  ?-  -.e
    %cons  [$(e p.e) $(e q.e)]
    %frag  [%frag axe.e $(e of.e)]
    %edit  [%edit axe.e $(e tgt.e) $(e val.e)]
    %quot  e
    %bump  [%bump $(e atm.e)]
    %deep  [%deep $(e val.e)]
    %same  [%same $(e a.e) $(e b.e)]
    %cond  [%cond $(e t.e) $(e y.e) $(e n.e)]
    %letn  [%letn $(e val.e) $(e in.e, env (bind-lam nam.e env))]
    %lamb  [%lamb $(e bod.e, env (bind-lam arg.e env))]
    %appl  [%appl $(e lam.e) $(e arg.e)]
    %delt  [%delt $(e bod.e, env (bind-del arg.e env))]
    %appd  [%appd $(e del.e) $(e arg.e)]
    %sint  [%sint tag.e $(e exp.e)]
    %dint  [%dint tag.e $(e clu.e) $(e exp.e)]
  ==
++  core-to-punk
  |=  e=core
  ::  =-  ~&  [%core exp=e pro=-]  -
  ^-  *  ::  punk
  ?-  -.e
    ^      [$(e p.e) $(e q.e)]
    %name  =/  f=*
             :-  0
             ?:  =(0 lex.e)  1  :: the backquote subject
             ::  subject is a list of bound values
             ::  lex 1s (tails) followed by a head (0)
             (lsh [0 1] (dec (lsh [0 lex.e] 1)))
           ?:  =(0 dex.e)  f
           :-  1
           =|  i=@
           |-  ^-  *
           ?:  =(i dex.e)  f
           $(i +(i), f [',' f])
    %frag  [7 $(e of.e) 0 axe.e]
    %edit  [10 [axe.e $(e tgt.e)] $(e val.e)]
    %quot  [1 val.e]
    %deep  [3 $(e val.e)]
    %bump  [4 $(e atm.e)]
    %same  [5 $(e a.e) $(e b.e)]
    %cond  [6 $(e t.e) $(e y.e) $(e n.e)]
    %letn  [8 $(e val.e) $(e in.e)]
    %lamb  [[1 $(e bod.e)] 0 1]
    %appl  [7 [$(e lam.e) $(e arg.e)] 2 [[0 3] 0 5] 0 4]
    %delt  ['`' $(e bod.e)]
    %appd  [2 $(e arg.e) $(e del.e)]
    %sint  [11 tag.e $(e exp.e)]
    %dint  [11 [tag.e $(e clu.e)] $(e exp.e)]
  ==
++  user-to-nock
  |=  e=user
  %-  compile:punk
  %-  core-to-punk
  %-  user-to-core
  e
++  tape-to-user
  |=  t=tape
  %-  parse
  %-  read
  %-  tokenize
  t
++  run-tape
  |=  t=tape
  .*  ~  ::  the "default environment" is "empty"
  %-  user-to-nock
  %-  tape-to-user
  t
--
:-  %say
|=  [^ [pgm=tape ~] ~]
:-  %noun
?>  .=  42
    .*  ~  (user-to-nock %appl [%lamb %a %a] %quot 42)
?>  .=  42
    (lsdectape "24")
?>  .=  [42 63]
    .*  63
    (run-tape "(let x 42 (dfn y (cons x y)))")
(run-tape pgm)
==
