/-  loon-read
=,  loon-read
^?
|%
+$  band  ::  battery definition
  $^  [p=band q=band]
  [~ nam=@t exp=uexp]
+$  barn  ::  battery names
  $@  @t
  [p=barn q=barn]
+$  bond
  $@  @t
  $%  [%cell n=@t l=bond r=bond]
      [%core n=@t bat=barn pay=bond]
  ==
+$  uexp
  $~  %a
  $@  @t
  $%  [%cons p=uexp q=uexp]
      [%frag axe=@ of=uexp]
      [%edit axe=@ tgt=uexp val=uexp]
      [%litn val=*]
      [%bump atm=uexp]
      [%deep val=uexp]
      [%same a=uexp b=uexp]
      [%cond t=uexp y=uexp n=uexp]
      [%peer nam=bond at=uexp in=uexp]
      [%letn nam=bond val=uexp in=uexp]
      [%rlet arm=band in=uexp]
      [%lamb nam=@t arg=bond bod=uexp]
      [%appl lam=uexp arg=uexp]
      [%delt arg=bond bod=uexp]
      [%nock fol=uexp arg=uexp]
      [%core arm=band]
      [%pull axe=@ cor=uexp]
      [%spot s=spot exp=uexp]
      [%sint tag=@ exp=uexp]
      [%dint tag=@ clu=uexp exp=uexp]
  ==
+$  prog  [arg=bond exp=uexp]
+$  mote  ?(%prog %uexp %sqar %appl %bug)
+$  trak  (list [mot=mote loc=spam])
+$  desc  ?(~ %main-args %many)
+$  parse-err  [des=desc tac=trak]
+$  parse-tape-err  (each read-tape-err parse-err)
--
