/-  psur=loon-parse, csur=loon-compile, plib=loon-parse
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
  =/  p  $(ram p.ram, axe (peg 2 axe))
  ?.  ?=(~ p)  p
  $(ram q.ram, axe (peg 3 axe))
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
    ?~  ctx  ~
    =;  her
      ?.  ?=(~ her)  her
      $(del +(del), ctx t.ctx)
    =*  bon  i.ctx
    =/  axe=@  1
    |-  ^-  path
    ?-  bon
        @
      ?.  =(n bon)  ~
      [del %leg axe]  
        [%cell *]
      =/  l  $(bon p.bon, axe (peg 2 axe))
      ?.  ?=(~ l)  l
      $(bon q.bon, axe (peg 3 axe))
        [%core *]
      =/  arm  (rind bat.bon n)
      ?~  arm  $(bon pay.bon, axe (peg axe 3))
      [del %arm rec=axe arm=(peg 2 arm)]
        [%also *]
      =/  fax  (rind new.bon n)
      ?~  fax  $(bon old.bon)
      =/  inx=@  (peg axe.bon fax)
      ?~  del.bon  [del (peg axe inx)]
      [(add del del.bon) inx]
    ==
  ++  die
    |=  cud=crud
    [%| tac cud]
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
             &+edit+tgt^val
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
      %cond  %+  b  r(e t.e)  |=  t=kern
             %+  b  r(e y.e)  |=  y=kern
             %+  b  r(e n.e)  |=  n=kern
             &+cond+t^y^n
      %with  %+  b  r(e val.e)  |=  val=kern
             %+  b  r(e in.e, i.ctx (lift nam.e))
             |=  do=kern  &+with+val^do
      %letn  %+  b  r(e val.e)  |=  val=kern
             %+  b  r(e in.e, i.ctx [%cell (lift nam.e) i.ctx])
             |=  in=kern  &+letn+val^in
      %letr  %+  b  (wear arm.e)        |=  [bat=kern b=bond]
             %+  b  r(e in.e, i.ctx b)  |=  in=kern
             &+letr+cor^in
      %bind  =/  p=path  (find nam.e)
             ?~  p  (die %find nam.e)
             ?:  ?=(%arm +<.p)  (die %barm nam.e)
             r(e bod.e, i.ctx [%also to.e [del.p leg.f.p] i.ctx])
      %lamb  ?~  nam.e
               %+  b  r(e bod.e, i.ctx [%cell (lift arg.e) i.ctx])
               |=  bod=kern  &+lamb+bod
             r(e [%letr [~ nam.e %lamb ~ arg.e bod.e] nam.e])
      %appl  %+  b  r(e lam.e)  |=  lam=kern
             %+  b  r(e arg.e)  |=  arg=kern
             &+appl+lam^arg
      %delt  %+  b  r(e bod.e, ctx [(lift arg.e) ctx])
             |=  bod=kern  &+delt+bod
      %nock  %+  b  r(e fol.e)  |=  fol=kern
             %+  b  r(e arg.e)  |=  arg=kern
             &+nock+fol^arg
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
--
