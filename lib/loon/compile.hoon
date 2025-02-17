/-  psur=loon-parse, csur=loon-compile
/+  plib=loon-parse
=,  psur
=,  csur
=,  plib
^?
|%
++  rind  ::  find the axis of a name in a tram
  =/  axe=@  1
  |=  [ram=tram n=@t]
  ^-  @
  ?@  ram  ?:(=(n ram) axe 0)
  =/  p  $(ram p.ram, axe (peg axe 2))
  ?.  ?=(~ p)  p
  $(ram q.ram, axe (peg axe 3))
++  lift  ::  bond is a strict superset of tram
  |=  t=tram
  ^-  bond
  ?@  t  t
  [%cell $(t p.t) $(t q.t)]
++  uk  ::  uexp -> kern
  =|  tac=trac
  |_  ctx=text
  ++  wear  ::  compile arms and return their bond
    |=  arm=band
    ^-  (coma [bat=kern bon=bond])
    =+  |-  ^-  [n=tram u=uexp]
        ?~  -.arm  +.arm
        =/  l  $(arm p.arm)
        =/  r  $(arm q.arm)
        [[n.l n.r] %cons u.l u.r]
    =.  i.ctx  [%core n i.ctx]
    %+  bach  (mint u)  |=  k=kern
    &+k^i.ctx
  ++  find  ::  resolve a name from ctx
    =|  del=@
    |=  n=@t
    ^-  path
    =;  her
      ?.  ?=(~ her)  her
      ?~  t.ctx  ~
      $(del +(del), ctx t.ctx)
    =*  bon  i.ctx
    =/  axe=@  1
    |-  ^-  path
    ?-  bon
        @
      ?.  =(n bon)  ~
      [del %leg axe]  
        [%cell *]
      =/  l  $(bon p.bon, axe (peg axe 2))
      ?.  ?=(~ l)  l
      $(bon q.bon, axe (peg axe 3))
        [%core *]
      =/  arm  (rind bat.bon n)
      ?~  arm  $(bon pay.bon, axe (peg axe 3))
      [del %arm rec=axe arm=(peg 2 arm)]
        [%also *]
      =/  fax  (rind new.bon n)
      ?~  fax  $(bon old.bon)
      =/  inx=@  (peg axe.bon fax)
      ?~  del.bon  [del leg+(peg axe inx)]
      [(add del del.bon) leg+inx]
    ==
  ++  die
    |=  cud=crud
    [%| tac cud]
  ++  cond  ::  helper for cond and case
    |=  [kul=(list [t=kern y=uexp]) els=(unit uexp)]
    ^-  (coma kern)
    =.  kul  (flop kul)
    ?~  kul  !!
    =*  r  $
    =*  t  t.i.kul
    %+  bach  (mint y.i.kul)  |=  y=kern
    ?~  t.kul
      ?~  els  &+cond+t^y^[%name 0 0]
      %+  bach  (mint u.els)  |=  n=kern
      &+cond+t^y^n
    %+  bach  r(kul t.kul)  |=  n=kern
    &+cond+t^y^n
  ++  mint
    |=  e=uexp  
    ^-  (coma kern)
    =*  r  $
    =*  b  bach
    ?@  e
      ?~  e  (die %cab)
      =/  p=path  (find e)
      ?~  p  (die %find e)
      &+[%name del.p +.f.p]
    ?-  -.e
      %cons  %+  b  r(e p.e)  |=  p=kern
             %+  b  r(e q.e)  |=  q=kern
             &+p^q
      %frag  %+  b  r(e of.e)  |=  of=kern
             &+frag+axe.e^of
      %edit  %+  b  r(e tgt.e)  |=  tgt=kern
             %+  b  r(e val.e)  |=  val=kern
             &+edit+axe.e^tgt^val
      %litn  &+e
      %tape  &+litn+t.e
      %cord  &+litn+c.e
      %bump  %+  b  r(e atm.e)  |=  atm=kern
             &+bump+atm
      %deep  %+  b  r(e val.e)  |=  val=kern
             &+deep+val
      %same  %+  b  r(e a.e)  |=  a=kern
             %+  b  r(e b.e)  |=  b=kern
             &+same+a^b
      %if    %+  b  r(e t.e)  |=  t=kern
             %+  b  r(e y.e)  |=  y=kern
             %+  b  r(e n.e)  |=  n=kern
             &+cond+t^y^n
      %cond  =/  l  col.e
             =|  out=(list [kern uexp])
             |-  ^-  (coma kern)
             %+  b  r(e t.i.l)  |=  t=kern
             =.  out  [[t y.i.l] out]
             ?^  t.l  ^$(l t.l)
             (cond out els.e)
      %case  =/  p=path  (find of.e)
             ?~  p  (die %find of.e)
             ?:  ?=(%arm +<.p)  (die %carm of.e)
             =/  n  [%name del.p leg.f.p]
             =/  l  do.e
             =|  out=(list [kern uexp])
             |-  ^-  (coma kern)
             =.  out  :_   out  :_  bod.i.l
               [%same [%litn val.i.l] n]
             ?^  t.l  $(l t.l)
             (cond out els.e)
      %with  %+  b  r(e val.e)  |=  val=kern
             %+  b  r(e do.e, i.ctx (lift nam.e))
             |=  do=kern  &+with+val^do
      %letn  =/  s
               =/  pag=page  p.e
               |-  ^-  sent
               ?@  -.pag  s.pag
               =/  p  $(pag p.pag)
               =/  q  $(pag q.pag)
               [[sub.p sub.q] %cons ped.p ped.q]
             %+  b  r(e ped.s)  |=  val=kern
             %+  b  r(e in.e, i.ctx [%cell (lift sub.s) i.ctx])
             |=  in=kern  &+letn+val^in
      %lets  %=  r  e
               :+  %letn  i.b.e
               ?~  t.b.e  in.e
               [%lets t.b.e in.e]
             ==
      %letr  %+  b  (wear arm.e)          |=  [bat=kern bon=bond]
             %+  b  r(e in.e, i.ctx bon)  |=  in=kern
             &+letr+bat^in
      %bind  =/  p=path  (find leg.e)
             ?~  p  (die %find leg.e)
             ?:  ?=(%arm +<.p)  (die %barm leg.e)
             r(e bod.e, i.ctx [%also to.e [del.p leg.f.p] i.ctx])
      %lamb  ?~  nam.e
               %+  b  r(e bod.e, i.ctx [%cell (lift arg.e) i.ctx])
               |=  bod=kern  &+lamb+bod
             r(e [%letr [~ nam.e %lamb %$ arg.e bod.e] nam.e])
      %appl  %+  b  r(e lam.e)  |=  lam=kern
             %+  b  r(e arg.e)  |=  arg=kern
             &+appl+lam^arg
      %delt  %+  b  r(e bod.e, ctx [(lift arg.e) ctx])
             |=  bod=kern  &+delt+bod
      %nock  %+  b  r(e fol.e)  |=  fol=kern
             %+  b  r(e arg.e)  |=  arg=kern
             &+nock+fol^arg
      %line  ?~  t.ctx  (die %top-line)
             =/  p=path  (find(ctx t.ctx) mac.e)
             ?.  ?=([@ %leg *] p)  (die %line mac.e p)
             %+  b  r(e arg.e)  |=  arg=kern
             &+line+[del.p^leg.f.p arg]
      %core  %+  b  (wear arm.e)  |=  [bat=kern *]
             &+core+bat
      %pull  %+  b  r(e cor.e)  |=  cor=kern
             &+pull+axe.e^cor
      %spot  %+  b  r(e exp.e, tac [s.e tac])  |=  exp=kern
             &+dint+spot+[%litn s.e]^exp
      %sint  %+  b  r(e exp.e)  |=  exp=kern
             &+sint+tag.e^exp 
      %dint  %+  b  r(e clu.e)  |=  clu=kern
             %+  b  r(e exp.e)  |=  exp=kern
             &+dint+tag.e^clu^exp 
    ==
  --
++  unq
  |=  [del=@ axe=@]
  =/  f=*  [0 axe]
  ?~  del  f
  :-  1
  =|  i=@
  |-  ^-  *
  ?:  =(i del)  f
  $(i +(i), f [',' f])
++  kp  ::  kern -> punk
  |=  e=kern
  ^-  *  ::  punk
  ?-  -.e
    ^      =-  ?@  -<  $(e -)
               [$(e p) $(e q)]
           |-  ^-  kern
           =?  q.e  ?=(^ -.q.e)  $(e q.e)  :: right-assoc
           ?+  e  e
             [[%litn *] %litn *]  [%litn val.p.e val.q.e]
             [[%name * @] %name * @]
               ?:  ?&  =(del.p.e del.q.e)
                       =(+(how.p.e) how.q.e)
                       =((rsh [0 1] how.p.e) (rsh [0 1] how.q.e))
                   ==
                 [%name del.p.e (rsh [0 1] how.q.e)]
               e
           ==
    %name  ?@  how.e  (unq del.e how.e)
           [9 ['\'' arm.how.e] (unq del.e rec.how.e)]
    %frag  ?:  ?=([%name %0 @] of.e)  ::  small opt for frag of leg
             [0 (peg how.of.e axe.e)]
           [7 $(e of.e) 0 axe.e]
    ::  whenever input can determine the head of a cell,
    ::  like the axis of our edit here, we must hard quote it
    ::  to prevent punk from seeing it as an operator
    %edit  [10 [['\'' axe.e] $(e val.e)] $(e tgt.e)]
    %litn  [1 '\'' val.e]
    %deep  [3 $(e val.e)]
    %bump  [4 $(e atm.e)]
    %same  [5 $(e a.e) $(e b.e)]
    %cond  [6 $(e t.e) $(e y.e) $(e n.e)]
    %with  [7 $(e val.e) $(e do.e)]
    %letn  [8 $(e val.e) $(e in.e)]
    %letr  [8 [1 $(e bat.e)] $(e in.e)]
    %lamb  [[1 $(e bod.e)] 0 1]
    %appl  [7 [$(e lam.e) $(e arg.e)] 2 [[0 3] 0 5] 0 4]
    %delt  ['`' $(e bod.e)]
    %nock  [2 $(e arg.e) $(e fol.e)]
    %line  =-  ::  optimize [7 [0 1] a] to just a
               ?:  =([%name 0 1] arg.e)  -
               [7 $(e arg.e) -]
           :-  ','
           =/  [i=@ a=*]  [0 0 axe.e]
           |-  ^-  *
           ?:  =(i del.e)  a
           $(i +(i), a [',' a])
    %core  [[1 $(e bat.e)] 0 1]
    %pull  [9 ['\'' axe.e] $(e cor.e)]
    %sint  [11 ['\'' tag.e] $(e exp.e)]
    %dint  [11 [['\'' tag.e] $(e clu.e)] $(e exp.e)]
  ==
++  pretty-compile-err
  |=  e=compile-err
  ^-  tang
  :_  (turn tac.e rend-spot)
  :-  %leaf
  =*  c  cud.e
  ?-  c
    %top-line  "cannot inline at top level"
    %cab       "cannot use _ as a variable"
    [%find *]  "unbound variable {<nam.c>}"
    [%barm *]  "cannot bind arm {<nam.c>}"
    [%carm *]  "cannot case scrutinize arm {<nam.c>}"
    [%line *]  ?~  p.c  "inline unbound variable {<nam.c>}"
               "cannot inline arm {<nam.c>}"
  ==
--
