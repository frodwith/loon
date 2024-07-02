/-  loon-read
=,  loon-read
^?
|%
+$  band  ::  battery definition
  $^  [p=band q=band]
  [~ nam=@t exp=uexp]
+$  tram  ::  tree of names
  $@  @t
  [p=tram q=tram]
+$  uexp
  $~  %a
  $@  @t  :: variable
  $%  [%cons p=uexp q=uexp]
      [%frag axe=@ of=uexp]
      [%edit axe=@ tgt=uexp val=uexp]
      [%litn val=*]
      [%tape t=tape]
      [%cord c=cord]
      [%bump atm=uexp]
      [%deep val=uexp]
      [%same a=uexp b=uexp]
      [%cond t=uexp y=uexp n=uexp]
      [%with nam=tram val=uexp do=uexp]
      [%letn nam=tram val=uexp in=uexp]
      [%letr arm=band in=uexp]
      [%bind leg=@t to=tram bod=uexp]
      [%lamb nam=@t arg=tram bod=uexp]
      [%appl lam=uexp arg=uexp]
      [%delt arg=tram bod=uexp]
      [%nock fol=uexp arg=uexp]
      [%core arm=band]
      [%pull axe=@ cor=uexp]
      [%spot s=spot exp=uexp]
      [%sint tag=@ exp=uexp]
      [%dint tag=@ clu=uexp exp=uexp]
  ==
+$  prog  [arg=tram exp=uexp]
+$  trak  (list [mot=@tas loc=spam])
+$  desc  ?(~ %none %many %alias)
+$  parse-err  [des=desc tac=trak]
+$  parse-tape-err  (each read-tape-err parse-err)
++  parm  |*(a=mold (each a parse-err))  :: parsing monad
--
