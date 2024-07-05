/-  psur=loon-parse
=,  psur
^?
|%
+$  fond
  $%  [%leg leg=@]
      [%arm rec=@ arm=@]
  ==
+$  fund  $@(~ fond)
+$  path  $@(~ [del=@ f=fond])
+$  bond
  $@  @t
  $%  [%cell p=bond q=bond]
      [%core bat=tram pay=bond]
      [%also new=tram [del=@ axe=@] old=bond]
  ==
+$  text  (lest bond)
+$  kern
  $~  [%name 0 0]
  $^  [p=kern q=kern]
  $%  [%name del=@ how=$@(@ [rec=@ arm=@])]
      [%frag axe=@ of=kern]
      [%edit axe=@ tgt=kern val=kern]
      [%litn val=*]
      [%deep val=kern]
      [%bump atm=kern]
      [%same a=kern b=kern]
      [%cond t=kern y=kern n=kern]
      [%with val=kern do=kern]
      [%letn val=kern in=kern]
      [%letr bat=kern in=kern]
      [%lamb bod=kern]
      [%appl lam=kern arg=kern]
      [%delt bod=kern]
      [%nock fol=kern arg=kern]
      [%line [del=@ axe=@] arg=kern]
      [%core bat=kern]
      [%pull axe=@ cor=kern]
      [%sint tag=@ exp=kern]
      [%dint tag=@ clu=kern exp=kern]
  ==
+$  trac  (list spot)
++  crud  ::  compile-err description
  $@  ?(%cab %top-line)
  $%  [%find nam=@t]
      [%barm nam=@t]
      [%line nam=@t p=path]
  ==
+$  compile-err  [tac=trac cud=crud]
++  coma  |*(a=mold (each a compile-err))  ::  compiler monad
--
