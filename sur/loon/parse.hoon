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
+$  sent  [sub=tram ped=uexp]  ::  sentence - a binding element
+$  page                       ::  one or more parallel bindings
  $^  [p=page q=page]
  [~ s=sent]
+$  book  (lest page)          ::  sequential bindings
+$  doze  (lest [val=* bod=uexp])  ::  cases
+$  cole  (lest [t=uexp y=uexp])   ::  cond lines
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
      [%if t=uexp y=uexp n=uexp]
      [%cond col=cole els=(unit uexp)]
      [%case of=@t do=doze els=(unit uexp)]
      [%with nam=tram val=uexp do=uexp]
      [%letn p=page in=uexp]
      [%lets b=book in=uexp]
      [%letr arm=band in=uexp]
      [%bind leg=@t to=tram bod=uexp]
      [%lamb nam=@t arg=tram bod=uexp]
      [%appl lam=uexp arg=uexp]
      [%delt arg=tram bod=uexp]
      [%nock fol=uexp arg=uexp]
      [%line mac=@t arg=uexp]
      [%core arm=band]
      [%pull axe=@ cor=uexp]
      [%spot s=spot exp=uexp]
      [%sint tag=@ exp=uexp]
      [%dint tag=@ clu=uexp exp=uexp]
  ==
+$  trak  (list [mot=@tas loc=spam])
+$  desc  ?(~ %none %many %alias %else)
+$  parse-err  [des=desc tac=trak]
+$  parse-tape-err  (each read-tape-err parse-err)
++  parm  |*(a=mold (each a parse-err))  :: parsing monad
--
