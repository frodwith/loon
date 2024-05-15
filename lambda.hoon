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
+$  neet
  $@  @t
  [p=neet q=neet]
+$  subj
  $^  [p=subj q=subj]
  $%  [%leg n=@t]
      [%rec r=neet]
  ==
+$  fond
  $?  [%leg leg=@]
      [%arm rec=@ arm=@]
  ==
+$  fund  $@(~ fond)
+$  path  $@(~ [del=@ f=fond])
+$  env   (list subj)
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
      [%letn nam=neet val=user in=user]
      [%lamb arg=neet bod=user]
      [%appl lam=user arg=user]
      [%delt arg=neet bod=user]
      [%appd del=user arg=user]
      [%sint tag=@ exp=user]
      [%dint tag=@ clu=user exp=user]
  ==
+$  core
  $~  [%name 0 0]
  $^  [p=core q=core]
  $%  [%name dex=@ how=$@(leg=@ [rec=@ arm=@])]
      [%frag axe=@ of=core]
      [%edit axe=@ tgt=core val=core]
      [%litn val=*]
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
++  parse-neet
  |=  e=sexp
  ^-  neet
  ?@  e  ~|("number in binding tree {<e>}" !!)
  ?-  -.e
    %sym   +.e
    %list  ?~  +.e  ~|("empty binding tree" !!)
           =/  l=(lest sexp)  +.e
           |-  ^-  neet
           =/  h  ^$(e i.l)
           ?~  t.l  h
           [h $(l t.l)]
  ==
++  parse
  |=  e=sexp
  ^-  user
  ?@  e  litn+e
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
        %lit
      :-  %litn
      =-  (litl +.l)
      |%
      ++  one
        |=  e=sexp
        ^-  *
        ?@  e  e
        ?:  ?=(%sym -.e)  ~|("symbol in literal" !!)
        (litl +.e)
      ++  litl
        |=  es=(list sexp)       ^-  *
        ?~  es    ~              ::  () = ~
        ?~  t.es  (one i.es)     ::  (a) = a
        [(one i.es) $(es t.es)]  ::  dubious, but convenient...
      --
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
      [%letn (parse-neet nam) $(e &3.l) $(e &4.l)]
        %dcall
      ?>  =(3 (lent l))
      [%appd $(e &2.l) $(e &3.l)]
        %fn
      ?>  =(3 (lent l))
      =/  arg  &2.l
      [%lamb (parse-neet arg) $(e &3.l)]
        %dfn
      ?>  =(3 (lent l))
      =/  arg  &2.l
      [%delt (parse-neet arg) $(e &3.l)]
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
++  delv
  =/  axe=@  1
  |=  [t=subj n=@t]
  ^-  fund
  ?-  -.t
    ^     =/  l  $(axe (peg axe 2), t p.t)
          ?.  ?=(~ l)  l
          $(axe (peg axe 3), t q.t)
    %leg  ?:(=(n n.t) leg+axe ~)
    %rec  =+  [bat arm]=`[neet @]`[r.t 1]
          |-  ^-  fund
          ?@  bat  ?:(=(n bat) arm+axe^bat ~)
          =/  l  $(arm (peg arm 2), bat p.bat)
          ?.  ?=(~ l)  l
          $(arm (peg arm 3), bat q.bat)
  ==
++  find
  =|  del=@
  |=  [=env n=@t]
  ^-  path
  ?~  env  ~
  =/  u=fund   (delv i.env n)
  ?.  ?=(~ u)  [del u]
  $(env t.env, del +(del))
++  neet-subj
  |=  n=neet
  ^-  subj
  ?@  n  leg+n
  [$(n p.n) $(n q.n)]
++  bind-lam
  |=  [net=neet e=env]
  ^-  env
  =/  s  (neet-subj net)
  ?~  e  [[s leg+''] ~]
  [[s i.e] t.e]
++  user-to-core
  |=  e=user
  ::  =-  ~&  [%user exp=e pro=-]  -
  =|  =env
  |-  ^-  core
  ?@  e
    =/  p=path  (find env e)
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
    %letn  [%letn $(e val.e) $(e in.e, env (bind-lam nam.e env))]
    %lamb  [%lamb $(e bod.e, env (bind-lam arg.e env))]
    %appl  [%appl $(e lam.e) $(e arg.e)]
    %delt  [%delt $(e bod.e, env [(neet-subj arg.e) env])]
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
             ?@  how.e  [0 leg.how.e]
             [9 arm.how.e 0 rec.how.e]
           ?:  =(0 dex.e)  f
           :-  1
           =|  i=@
           |-  ^-  *
           ?:  =(i dex.e)  f
           $(i +(i), f [',' f])
    %frag  [7 $(e of.e) 0 axe.e]
    %edit  [10 [axe.e $(e tgt.e)] $(e val.e)]
    %litn  [1 val.e]
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
  $%  [%eval tape]
      [%load path]
  ==
:-  %say
|=  [^ [=cmd ~] ~]
:-  %noun
?-  cmd
    [%eval *]
  (run-tape +.cmd)
    [%load *]
  =/  w=wain  .^(wain %cx +.cmd)
  =/  c=cord  (of-wain:format w)
  =/  t=tape  (trip c)
  (run-tape t)
    %test
  ~|  t+0
  ?>  .=  42
      .*  ~  (user-to-nock %appl [%lamb %a %a] %litn 42)
  ~|  t+1
  ?>  .=  42
      (lsdectape "24")
  ~|  t+2
  ?>  .=  [42 63]  :: dfns can close over lexicals
      .*  63
      (run-tape "(let x 42 (dfn y (cons x y)))")
  ~|  t+3
  ?>  .=  [42 63]  :: dfns can close over dexicals
      %-  run-tape
      "(dcall (dcall (dfn x (dfn y (cons x y))) 42) 63)"
  ~|  t+'neet parse'
  ?>  .=  %x            (parse-neet (read "x"))
  ?>  .=  %x            (parse-neet (read "(x)"))
  ?>  .=  [%x %y]       (parse-neet (read "(x y)"))
  ?>  .=  [%x %y %z]    (parse-neet (read "(x y z)"))
  ?>  .=  [[%x %y] %z]  (parse-neet (read "((x y) z)"))
  ~|  t+%fst
  ?>  .=  40       (run-tape "((fn (x y) x) (cons 40 2))")
  ~|  t+%snd
  ?>  .=  2        (run-tape "((fn (x y) y) (cons 40 2))")
  ~|  t+'destructuring let'
  ?>  .=  5        (run-tape "(let (x y z) (lit 3 4 5) z)")
  ~|  t+'parallel let'
  ?>  .=  [2 40]   (run-tape "(let (x y) (cons 40 2) (cons y x))")
  ~|  t+%lits
  ?>  .=  [40 2]   (run-tape "(lit 40 2)")
  ?>  .=  [40 2]   (run-tape "(lit (40 2))")
  ?>  .=  42       (run-tape "(lit 42)")
  ?>  .=  42       (run-tape "(lit 42)")
  ?>  .=  42       (run-tape "(lit (42))")
  ~|  t+%id
  ?>  .=  42       (run-tape "((fn x x) 42)")
  ~|  t+%nest
  ?>  .=  [40 2]   (run-tape "(((fn x (fn y (cons x y))) 40) 2)")
  =/  dec-src=tape
    "(let fix (fn exp (let a (fn f (exp (fn x ((f f) x)))) (a a))) (let dec (fn n ((fix (fn rec (fn i (let up (bump i) (if (same up n) i (rec up)))))) 0)) (dec 43)))"
  ~|  [t+%dec (cram !>((compile-tape dec-src)))]
  ?>  =(42 (run-tape dec-src))
  %ok
==
==
