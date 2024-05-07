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
  $~  [%lamv 0]
  $^  [p=core q=core]
  $%  [%lamv inx=@]
      [%delv inx=@]
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
  $@  @ud  ::  lambda
  [~ @ud]  ::  delta
+$  env
  (map @t bind)
--
|%
++  extend
  |=  [nam=@ =env lam=?]
  %.  :-  nam
      ?:(lam 0 [~ 0])
  %~  put  by
  %-  ~(run by env)
  |=  a=bind
  ?@  a
    ?:(lam +(a) a)
  ?:(lam a `+.a)
++  user-compile
  |=  e=user
  ::  =-  ~&  [%user exp=e pro=-]  -
  =|  =env
  |-  ^-  core
  ?@  e
    =/  b  (~(got by env) e)
    ?@  b  [%lamv b]
    [%delv +.b]
  ?-  -.e
    %cons  [$(e p.e) $(e q.e)]
    %frag  [%frag axe.e $(e of.e)]
    %edit  [%edit axe.e $(e tgt.e) $(e val.e)]
    %quot  e
    %bump  [%bump $(e atm.e)]
    %deep  [%deep $(e val.e)]
    %same  [%same $(e a.e) $(e b.e)]
    %cond  [%cond $(e t.e) $(e y.e) $(e n.e)]
    %letn  [%letn $(e val.e) $(e in.e, env (extend nam.e env &))]
    %lamb  [%lamb $(e bod.e, env (extend arg.e env &))]
    %appl  [%appl $(e lam.e) $(e arg.e)]
    %delt  [%delt $(e bod.e, env (extend arg.e env |))]
    %appd  [%appd $(e del.e) $(e arg.e)]
    %sint  [%sint tag.e $(e exp.e)]
    %dint  [%dint tag.e $(e clu.e) $(e exp.e)]
  ==
++  core-compile
  |=  e=core
  ::  =-  ~&  [%core exp=e pro=-]  -
  ^-  *  ::  punk
  ?-  -.e
    ^      [$(e p.e) $(e q.e)]
           ::  subject is a list of bound values
           ::  i+1 1s (tails) followed by a head (0)
    %lamv  0+(lsh [0 1] (dec (lsh [0 +(inx.e)] 1)))
    %delv  :-  1
           =|  i=@
           |-  ^-  *
           :-  ','
           ?:  =(i inx.e)  [0 1]
           $(i +(i))
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
++  compile
  |=  e=user
  %-  compile:punk
  %-  core-compile
  %-  user-compile
  e
--
:-  %say
|=  [^ [exp=user ~] ~]
:-  %noun
?>  .=  42
    .*  ~  (compile %appl [%lamb %a %a] %quot 42)
=/  fol=*  (compile exp)
~&  fol
.*  ~  fol
==
