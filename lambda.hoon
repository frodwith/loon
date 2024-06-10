/+  punk
=~
::  the lambda-delta calculus is an augmentation of the untyped lambda calculus.
::  we start with abstraction and application (lamb/appl), and we add:
::    nouns (cons,1,3,4,5,10)
::    let (8 - the subject is a tree of bound values)
::    if-then-else (6)
::    hints (11)
::    delta abstraction and application (quasiquotes lambdas, delt/nock)
::      Delta abstractions are nock formulas.
::      It is legal to delta apply a noun (see the nock spec for semantics).
::  we compile to nock through punk, the quasiquote-nock.
|%
+$  token :: XX: add position info
  $@  ?(%'(' %')' %'[' %']')
  $%  [%sym @t]
      [%num @]
  ==
+$  sexp
  $@  @
  $%  [%sym @t]
      [%rond (list sexp)]
      [%sqar (list sexp)]
  ==
+$  toke-state
  $@  ~
  [?(%sym %num) (list @t)]
+$  tram
  $@  @t
  [n=@t l=tram r=tram]
+$  neet
  $@  @t
  [p=neet q=neet]
+$  bond
  $@  @t
  $%  [%cell n=@t l=bond r=bond]
      [%core bat=neet pay=bond]
  ==
+$  fond
  $?  [%leg leg=@]
      [%arm rec=@ arm=@]
  ==
+$  fund  $@(~ fond)
+$  path  $@(~ [del=@ f=fond])
+$  gamma  (lest bond)
+$  raph
  $^  [p=raph q=raph]
  [~ nam=@t exp=user]
+$  user
  $~  %a
  $@  @t
  $%  [%cons p=user q=user]
      [%frag axe=@ of=user]
      [%edit axe=@ tgt=user val=user]
      [%litn val=*]
      [%bump atm=user]
      [%deep val=user]
      [%same a=user b=user]
      [%cond t=user y=user n=user]
      [%letn nam=tram val=user in=user]
      [%letr g=raph in=user]
      [%lamb arg=tram bod=user]
      [%recl nam=@t arg=tram bod=user]
      [%appl lam=user arg=user]
      [%delt arg=tram bod=user]
      [%nock arg=user del=user]
      [%sint tag=@ exp=user]
      [%dint tag=@ clu=user exp=user]
  ==
+$  core
  $~  [%name 0 0]
  $^  [p=core q=core]
  $%  [%name dex=@ how=$@(@ [rec=@ arm=@])]
      [%frag axe=@ of=core]
      [%edit axe=@ tgt=core val=core]
      [%litn val=*]
      [%deep val=core]
      [%bump atm=core]
      [%same a=core b=core]
      [%cond t=core y=core n=core]
      [%letn val=core in=core]
      [%letr rec=core in=core]
      [%lamb bod=core]
      [%appl lam=core arg=core]
      [%delt bod=core]
      [%nock arg=core del=core]
      [%sint tag=@ exp=core]
      [%dint tag=@ clu=core exp=core]
  ==
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
  ?:  =('[' c)
    $(out [%'[' (tok-fin st out)], st ~)
  ?:  =(']' c)
    $(out [%']' (tok-fin st out)], st ~)
  ?:  =('_' c)
    $(out [[%sym %$] (tok-fin st out)], st ~)
  ?:  |(=(' ' c) =('\0a' c))
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
  |=  in=tape
  (read-tokens (tokenize in))
++  read-tokens
  |=  in=(list token)
  =/  stk=(lest (pair ?(%top %rond %sqar) (list sexp)))  ~[top+~]
  |-  ^-  sexp
  ?~  in
    ::  stack should have one item in it, or we left out a )]
    ?.  ?=(~ t.stk)      ~|('unclosed group' !!)
    ?~  q.i.stk          ~|('no expression' !!)
    ?.  ?=(~ t.q.i.stk)  ~|('too many expressions' !!)
    i.q.i.stk
  =/  t  i.in
  =>  .(in t.in)
  ?-  t
      %'('
    $(stk [rond+~ stk])
      %'['
    $(stk [sqar+~ stk])
      [%sym *]
    $(q.i.stk [[%sym +.t] q.i.stk])
      [%num *]
    $(q.i.stk [+.t q.i.stk])
      %')'
    ?-  p.i.stk
        %top   ~|('unmatched closing paren' !!)
        %sqar  ~|('closing bracket with paren' !!)
        %rond
      ?<  ?=(~ t.stk)  ::  would be %top
      $(stk t.stk(q.i [rond+(flop q.i.stk) q.i.t.stk]))
    ==
      %']'
    ?-  p.i.stk
        %top   ~|('unmatched closing bracket' !!)
        %rond  ~|('closing paren with bracket' !!)
        %sqar
      ?<  ?=(~ t.stk)  ::  would be %top
      $(stk t.stk(q.i [sqar+(flop q.i.stk) q.i.t.stk]))
    ==
  ==
++  tram-sqar
  |=  l=(list sexp)
  ^-  (unit [tram tram])
  ?~  l    ~
  ?~  t.l  ~
  =/  hed  (parse-tram i.l)
  ?~  hed  ~
  =/  l=(lest sexp)  t.l
  =-  ?~  -  ~
      `[u.hed u]
  |-  ^-  (unit tram)
  =/  one  (parse-tram i.l)
  ?~  one  ~
  ?~  t.l  one
  =/  mor  $(l t.l)
  ?~  mor  ~
  `[%$ u.one u.mor]
++  parse-tram
  |=  e=sexp
  ^-  (unit tram)
  ?+  e  ~
      [%sym *]
    `+.e
      [%sqar *]
    =/  sq  (tram-sqar +.e)
    ?~  sq  ~
    `[%$ u.sq]
      [%rond [%sym @] * *]
    =/  cel=(unit [tram tram])
      =*  mor  t.e
      ?~  t.mor  :: if there's only one more thing, must be square
        ?.  ?=([%sqar *] i.mor)  ~
        (tram-sqar +.i.mor)
      (tram-sqar mor)  :: "insert" square
    ?~  cel  ~
    `[+.i.+.e u.cel]
  ==
++  parse-raph
  |=  e=sexp
  ?>  ?=([%rond *] e)
  =/  es=(list sexp)  +.e
  |-  ^-  raph
  ?~  es    !!
  ?~  t.es  ^$(e i.es)
  ?:  ?=([%sym *] i.es)
    ?>  ?=([* ~] t.es)
    [~ +.i.es (parse i.t.es)]
  [^$(e i.es) $(es t.es)]
++  june
  |=  [a=user b=user]
  ^-  user
  ?.  &(?=([%litn *] a) ?=([%litn *] b))
    [%cons a b]
  [%litn val.a val.b]
++  massage-args
  |=  arg=(list sexp)
  ^-  sexp
  ?~  arg  ~|('empty argument list' !!)
  ?~  t.arg  i.arg
  [%sqar arg]
++  parse
  |=  e=sexp
  ^-  user
  ?@  e  litn+e
  ?-  -.e
      %sym  +.e
      %sqar
    =*  l  +.e
    ?~  l  ~|('empty brackets' !!)
    ?~  t.l  ~|('singleton brackets' !!)
    %+  june  $(e i.l)
    =/  p=(lest sexp)  t.l
    |-  ^-  user
    =/  one  ^$(e i.p)
    ?~  t.p  one
    (june one $(p t.p))
      %rond
    =*  l  +.e
    =/  op  &1.l
    ?.  ?=([%sym *] op)
      ?>  (gth (lent l) 1)
      [%appl $(e op) $(e (massage-args +.l))]
    ?+  +.op  ~|  l
              ?>  (gth (lent l) 1)
              [%appl +.op $(e (massage-args +.l))]
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
      [%letn (need (parse-tram nam)) $(e &3.l) $(e &4.l)]
        %letrec
      ?>  =(3 (lent l))
      [%letr (parse-raph &2.l) $(e &3.l)]
        %nock
      ?>  =(3 (lent l))
      [%nock $(e &2.l) $(e &3.l)]
        %fn
      =/  len  (lent l)
      ?+  len  ~|("fn has {<len>} args" !!)
        %3  [%lamb (need (parse-tram &2.l)) $(e &3.l)]
        %4  =/  nex  &2.l
            ?>  ?=([%sym *] nex)
            [%recl +.nex (need (parse-tram &3.l)) $(e &4.l)]
      ==
        %dfn
      ?>  =(3 (lent l))
      =/  arg  &2.l
      [%delt (need (parse-tram arg)) $(e &3.l)]
        %sint
      ?>  =(3 (lent l))
      =/  tag  &2.l
      ?>  ?=(@ tag)
      [%sint tag $(e &3.l)]
        %dint
      ?>  =(4 (lent l))
      =/  tag  &2.l
      ?>  ?=(@ tag)
      [%dint tag $(e &3.l) $(e &4.l)]
    ==
  ==
++  bond-delv
  =/  axe=@  1
  |=  [b=bond n=@t]
  ^-  fund
  ?-  b
      @
    ?.  =(n b)  ~
    leg+axe
      [%cell *]
    ?:  =(n n.b)  leg+axe
    =/  l  $(b l.b, axe (peg axe 2))
    ?.  ?=(~ l)  l
    $(b r.b, axe (peg axe 3))
      [%core *]
    =/  fib=fund  :: found in battery
      =/  arm=@  2
      =/  bat=neet  bat.b
      |-  ^-  fund
      ?@  bat  ?:(=(n bat) [%arm axe arm] ~)
      =/  l  $(arm (peg 2 arm), bat p.bat)
      ?.  ?=(~ l)  l
      $(arm (peg arm 3), bat q.bat)
    ?.  ?=(~ fib)  fib
    $(b pay.b, axe (peg axe 3))
  ==
++  gamma-find
  =|  del=@
  |=  [g=gamma n=@t]
  ^-  path
  =/  u=fund   (bond-delv i.g n)
  ?.  ?=(~ u)  [del u]
  ?~  t.g    ~
  $(g t.g, del +(del))
++  tram-to-bond
  |=  t=tram
  ^-  bond
  ?@  t  t
  [%cell n.t $(t l.t) $(t r.t)]
++  extend-tram
  |=  [g=gamma t=tram]
  ^-  gamma
  [[%cell %$ (tram-to-bond t) i.g] t.g]
++  user-to-core
  |=  e=user
  ::  =-  ~&  [%user exp=e pro=-]  -
  =|  g=gamma
  |-  ^-  core
  ?@  e
    ?~  e  ~|("empty symbol (_) in variable position" !!)
    =/  p=path  (gamma-find g e)
    ?~  p  ~|("unbound name {<e>}" !!)
    [%name del.p +>.p]
  ?-  -.e
    %cons  [$(e p.e) $(e q.e)]
    %frag  [%frag axe.e $(e of.e)]
    %edit  [%edit axe.e $(e tgt.e) $(e val.e)]
    %litn  e
    %bump  [%bump $(e atm.e)]
    %deep  [%deep $(e val.e)]
    %same  [%same $(e a.e) $(e b.e)]
    %cond  [%cond $(e t.e) $(e y.e) $(e n.e)]
    %letn  [%letn $(e val.e) $(e in.e, g (extend-tram g nam.e))]
    %letr  =+  =/  rap  g.e
               |-  ^-  [n=neet u=user]
               ?~  -.rap  +.rap
               =/  l  $(rap p.rap)
               =/  r  $(rap q.rap)
               [[n.l n.r] %cons u.l u.r]
           =.  g  [[%core n i.g] t.g]
           [%letr $(e u) $(e in.e)]
    %lamb  [%lamb $(e bod.e, g (extend-tram g arg.e))]
    %recl  $(e [%letr [~ nam.e %lamb arg.e bod.e] nam.e])
    %appl  [%appl $(e lam.e) $(e arg.e)]
    %delt  [%delt $(e bod.e, g [(tram-to-bond arg.e) g])]
    %nock  [%nock $(e arg.e) $(e del.e)]
    %sint  [%sint tag.e $(e exp.e)]
    %dint  [%dint tag.e $(e clu.e) $(e exp.e)]
  ==
++  unq
  |=  [dex=@ axe=@]
  =/  f=*  [0 axe]
  ?~  dex  f
  :-  1
  =|  i=@
  |-  ^-  *
  ?:  =(i dex)  f
  $(i +(i), f [',' f])
++  core-to-punk
  |=  e=core
  ::  =-  ~&  [%core exp=e pro=-]  -
  ^-  *  ::  punk
  ?-  -.e
    ^      [$(e p.e) $(e q.e)]
    %name  ?@  how.e  (unq dex.e how.e)
           [9 ['\'' arm.how.e] (unq dex.e rec.how.e)]
    %frag  [7 $(e of.e) 0 axe.e]
    ::  whenever input can determine the head of a cell,
    ::  like the axis of our edit here, we must hard quote it
    ::  to prevent punk from seeing it as an operator
    %edit  [10 [['\'' axe.e] $(e val.e)] $(e tgt.e)]
    %litn  [1 '\'' val.e]
    %deep  [3 $(e val.e)]
    %bump  [4 $(e atm.e)]
    %same  [5 $(e a.e) $(e b.e)]
    %cond  [6 $(e t.e) $(e y.e) $(e n.e)]
    %letn  [8 $(e val.e) $(e in.e)]
    %letr  [8 [1 $(e rec.e)] $(e in.e)]
    %lamb  [[1 $(e bod.e)] 0 1]
    %appl  [7 [$(e lam.e) $(e arg.e)] 2 [[0 3] 0 5] 0 4]
    %delt  ['`' $(e bod.e)]
    %nock  [2 $(e arg.e) $(e del.e)]
    %sint  [11 ['\'' tag.e] $(e exp.e)]
    %dint  [11 [['\'' tag.e] $(e clu.e)] $(e exp.e)]
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
  t
++  compile-tape
  |=  t=tape
  %-  user-to-nock
  %-  tape-to-user
  t
++  run-tape
  |=  t=tape
  .*  ~  ::  the "default environment" is "empty"
  (compile-tape t)
++  cram
  |=  v=vase
  ~(ram re (sell v))
++  run-slog
  |=  t=tape
  =/  u=user  (tape-to-user t)
  ~&  user=(cram !>(u))
  =/  n=*  (user-to-nock u)
  ~&  nock=(cram !>(n))
  .*(~ n)
--
=/  cmd
  $@  %test
  $%  [%read tape]
      [%eval tape]
      [%load path]
  ==
:-  %say
|=  [^ [=cmd ~] ~]
:-  %noun
?-  cmd
    [%read *]
  (read +.cmd)
    [%eval *]
  (run-tape +.cmd)
    [%load *]
  =/  w=wain  .^(wain %cx +.cmd)
  =/  c=cord  (of-wain:format w)
  =/  t=tape  (trip c)
  (run-tape t)
    %test
  ~|  t+'raph parse'
  ?>  .=  [~ %x %litn 12]  (parse-raph (read "(x 12)"))
  ?>  .=  [~ %x %litn 12]  (parse-raph (read "((x 12))"))
  ?>  .=  [[~ %x %litn 40] ~ %y %litn 2]
      (parse-raph (read "((x 40) (y 2))"))
  ~|  t+0
  ?>  .=  42
      .*  ~  (user-to-nock %appl [%lamb %a %a] %litn 42)
  ~|  t+1
  ?>  .=  42
      (lsdectape "24")
  ~|  t+2
  ?>  .=  [42 63]  :: dfns can close over lexicals
      .*  63
      (run-tape "(let x 42 (dfn y [x y]))")
  ~|  t+3
  ?>  .=  [42 63]  :: dfns can close over dexicals
      %-  run-tape
      "(nock 63 (nock 42 (dfn x (dfn y [x y]))))"
  ~|  t+"literal nock formula"
  ?>  .=  42
      %-  run-tape
      "(nock 41 [4 0 1])"
  ~|  t+'read'
  ?>  .=  [%rond 1 2 3 ~]          (read "(1 2 3)")
  ?>  .=  [%sqar 1 2 3 ~]          (read "[1 2 3]")
  ?>  .=  [%sqar 1 [%rond ~] 3 ~]  (read "[1 () 3]")
  ~|  t+'tram parse'
  =/  ptr  |=(a=tape (parse-tram (read a)))
  ?>  .=  `%x
      (ptr "x")
  ?>  .=  `[%$ %x %y]
      (ptr "[x y]")
  ?>  .=  `[%$ %x %$ %y %z]
      (ptr "[x y z]")
  ?>  .=  `[%$ [%$ %x %y] %z]
      (ptr "[[x y] z]")
  ?>  .=  `[%foo [%bar %x %y] %z]
      (ptr "(foo [(bar [x y]) z])")
  ?>  =(~ (ptr "(foo x)"))
  ?>  =(~ (ptr "(foo (bar [x y]))"))
  ~|  t+%fst
  ?>  .=  40       (run-tape "((fn [x y] x) [40 2])")
  ?>  .=  40       (run-tape "((fn [x _] x) [40 2])")
  ~|  t+%snd
  ?>  .=  2        (run-tape "((fn [x y] y) [40 2])")
  ?>  .=  2        (run-tape "((fn [_ y] y) [40 2])")
  ~|  t+'destructuring let'
  ?>  .=  5        (run-tape "(let [x y z] [3 4 5] z)")
  ?>  .=   [3 4 5 [4 5] 3 4 5]
      %-  run-tape
      "(let (foo [x (bar [y z])]) [3 4 5] [x y z bar foo])"
  ?>  .=   [3 4 5 [4 5] 3 4 5]
      %-  run-tape
      "(let (foo x (bar y z)) [3 4 5] [x y z bar foo])"
  ~|  t+'parallel let'
  ?>  .=  [2 40]   (run-tape "(let [x y] [40 2] [y x])")
  ~|  t+%args
  ::  you may omit the brackets for cell args just like hoon
  ?>  .=  [0 42]
      %-  run-tape
      "((fn x x) 0 42)"
  ~|  t+%lits
  ?>  .=  [40 2]   (run-tape "[40 2]")
  ::  punk special characters inside lits must be hard quoted
  ?>  .=  [44 0 1]  (run-tape "[44 0 1]")
  ~|  t+%sqar
  ?>  .=  [1 40 2]
      (compile-tape "[40 2]")
  ?>  .=  [40 2]
      (run-tape "(let x 40 (let y 2 [x y]))")
  ~|  t+%edit
  ?>  .=  [1 42 3]
      (run-tape "(edit 6 [1 2 3] 42)")
  ::  axis ',' (44) tests a corner of punk
  ::  so first make sure its sibling works
  ?>  .=  [[1 2 [[3 4] 5]] 6]
      .*  [[1 2 [[3 13] 5]] 6]
      (run-tape "(dfn x (edit 45 x 4))")
  ::  now if we haven't quoted edit properly, this will fail
  ?>  .=  [[1 2 [[3 4] 5]] 6]
      .*  [[1 2 [[13 4] 5]] 6]
      (run-tape "(dfn x (edit 44 x 3))")
  ::  XX we should have a test for pulling axis 44, but don't yet
  ~|  t+%hints
  ?>  .=  42  (run-tape "(sint 44 42)")
  ?>  .=  42  (run-tape "(dint 44 0 42)")
  ~|  t+%id
  ?>  .=  42       (run-tape "((fn x x) 42)")
  ~|  t+%nest
  ?>  .=  [40 2]   (run-tape "(((fn x (fn y [x y])) 40) 2)")
  =/  dec-src=tape
    "(let fix (fn exp (let a (fn f (exp (fn x ((f f) x)))) (a a))) (let dec (fn n ((fix (fn rec (fn i (let up (bump i) (if (same up n) i (rec up)))))) 0)) (dec 43)))"
  ?.  =(42 (run-tape dec-src))
    ~|([t+%dec (cram !>((compile-tape dec-src)))] !!)
  ~|  t+%letrec
  ?>  =(42 (run-tape "(letrec (x 42) x)"))
  ~|  t+%'hold your breath, make a wish...'
  ?>  .=  3  %-  run-tape
    "(letrec (loop (fn x (if (same x 3) x (loop (bump x))))) (loop 1))"
  ~|  t+%'count to three, with sugar'
  ?>  .=  3  %-  run-tape
    "((fn loop x (if (same x 3) x (loop (bump x)))) 1)"
  =/  lrdec-src=tape
    "(let dec (fn n (letrec (loop (fn i (let up (bump i) (if (same up n) i (loop up))))) (loop 0))) (dec 43))"
  ?.  =(42 (run-tape lrdec-src))
    ~|([t+%lrdec (cram !>((compile-tape lrdec-src)))] !!)
  ~&  (cram !>((compile-tape lrdec-src)))
  ~|  t+%odd
  =/  ddec  %-  run-tape
"""
(dfn n
 ((fn loop i
   (let up (bump i)
    (if (same up n)
     i
     (loop up)))) 0))
"""
  ?>  =(42 .*(43 ddec))
::  this "module" "imports" dec (by taking it as an argument)
::  then it defines two mutually recursive dfns, odd and evn
::  and returns them
  =+  ^=  [odd even]  .*  ddec  %-  run-tape
"""
(dfn dec
 (letrec
  ((odd (dfn n (if (same 0 n) 1 (nock (nock n dec) evn))))
   (evn (dfn n (if (same 0 n) 0 (nock (nock n dec) odd)))))
  [odd evn]))
"""
  ?>  =(0 .*(42 even))
  ?>  =(1 .*(42 odd))
  ~|  t+"ffi"
  =/  fact-module  %-  run-tape
"""
(dfn [lth mul dec]
 (let slam (fn [cor sam] (nock (edit 6 cor sam) [9 2 0 1]))
  (dfn n
   ((fn fac n
     (if (slam lth n 2)
      1
      (slam mul n (fac (slam dec n)))))
    n))))
"""
  ?>  .=  120
      .*  5
      .*  [lth mul dec]
      fact-module
  %ok
==
==
