::  this appears to be a functioning multilevel quasiquote
::
::  33  !  compile
::  39  '  hard quote
::  44  ,  unquote
::  96  `  quasiquote
::
::  unquote(,) and quasiquote(`) are very direct analogues to lisp's
::  unquote-splicing shouldn't be necessary (nock isn't sequency)
::
::  hard quote(') splices its argument into the output unprocessed,
::  and should be used when constructing a punk formula dynamically
::  to avoid compiling subparts. For example, the axis in nock 10 could be
::  one of the special numbers and heads a cell, so should be hard quoted.
::
::  compile(!) makes punk formulas "first class" - you can build and
::  use them at runtime -- but be aware that using it injects the
::  punk compiler as a constant into the output nock formula.
=>  dec=dec
|%
+$  made  $@(~ [~ u=*])
++  compile
  |=  fol=*
  =/  u  (compile:lev fol)
  ?~  u  fol
  u.u
++  lev
  |_  lvl=@
  ++  delay
    |=  e=*
    =|  i=@
    |-  ^-  *
    ?:  =(i lvl)  e
    $(i +(i), e [1 e])
  ++  compile
    |=  fol=*
    =|  out=?
    |-  ^-  made  ::  ~ means fol is unchanged (avoid reconsing)
    ?@  fol  ~
    ?:  =('\'' -.fol)
      `(delay +.fol)
    ?:  =('`' -.fol)
      =>  .(lvl +(lvl), fol +.fol)
      =/  u  $
      ?~(u `(delay fol) u)
    ?:  =(',' -.fol)
      =/  f=*
        =>  .(out |, fol +.fol, lvl (dec lvl)) ::  underflow outside `
        =/  r  $
        ?~(r (delay fol) u.r)
      ::  add an extra layer of quoting for every level of nested unquote
      ::  so computed values "bubble out" to the appropriate stage
      :-  ~
      ?:  out  f
      [(delay 1) f]
    ?:  =('!' -.fol)
      =/  f
        =/  r  $(fol +.fol)
        ?~(r (delay +.fol) u.r)
      :*  ~  (delay 9)  (delay 2)  (delay 10)
          [(delay 6) f]
          (delay 1 ^compile)
      ==
    =/  l  $(fol -.fol)
    =/  r  $(fol +.fol)
    ?~  l  ?~  r  ~  `[(delay -.fol) u.r]
    ?~  r  `[u.l (delay +.fol)]
    `[u.l u.r]
  --
--
