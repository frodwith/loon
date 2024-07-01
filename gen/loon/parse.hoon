/-  psur=loon-parse
/+  plib=loon-parse, loon-read
=,  psur
=,  plib
=,  loon-read
:-  %say
|=  [^ ~ [in=tape ~]]
:-  %tang
=/  rend-spot
  |=  s=spot
  ^-  tank
  =*  l   p.q.s
  =*  r   q.q.s
  :~  %rose  [":" ~ ~]
      (smyt p.s)
      :~  %rose  ["." "<" ">"] 
          :~  %rose  [" " "[" "]"]
              leaf+(scow %ud p.l)
              leaf+(scow %ud q.l)
          ==
          :~  %rose  [" " "[" "]"]
              leaf+(scow %ud p.r)
              leaf+(scow %ud q.r)
          ==
      ==
  ==
=/  dump
  |=  err=parse-err
  =|  out=(list tank)
  =/  in  tac.err
  :-  ?~  des.err  leaf+"parse error"
      leaf+"{<des.err>}"
  |-  ^-  (list tank)
  ?~  in  (flop out)
  %=  $  in  t.in  out  :_  out
    :~  %rose  ["|" "" ""]
        leaf+"{<mot.i.in>}"
        ?~  loc.i.in
          leaf+"<no location>"
        (rend-spot loc.i.in)
    ==
  ==
?^  in
  =/  par  (parse-tape ~ in)
  ?:  ?=(%& -.par)  ~[leaf+"{<p.par>}"]
  ?:  ?=(%& -.p.par)  ~[leaf+(pretty-read-tape-err p.p.par)]
  (dump p.p.par)
=/  case=(list [name=tape exp=uexp t=tape])
  :~  :+  "number"  litn+12           "12"
      :+  "symbol"  %a                "a"
      :+  "tape"    tape+"hi"         "\"hi\""
      :+  "cord"    cord+'hi'         "'hi'"
      :+  "cell"    [%cons %a %b]     "[a b]"
      :+  "bump"    bump+litn+42      "(bump 42)"
      :+  "deep"    deep+%a           "(deep a)"
      :+  "same"    [%same %a %b]     "(same a b)"
      :+  "if"      [%cond %a %b %c]  "(if a b c)"
      :+  "with"    [%with [%$ %b] [%frag 3 %c] %b]
      "(with [_ b] (frag 3 c) b)"
      :+  "letn"
        :^  %letn  [[%a %$] %c]
          [%appl %foo %bar]
        [%cons %a %c]
      "(let [[a _] c] (foo bar) [a c])"
      :+  "letr single"  [%letr [~ %foo %a] %a]  "(rec (foo a) a)"
      :+  "letr multi"
        [%letr [[~ %foo %a] ~ %bar %b] %cons %foo %bar]
      "(rec [(foo a) (bar b)] [foo bar])"
      :+  "bind"  [%bind %d [[%a %b] %c] %cons %b %cons %c %a]
      "(bind d [[a b] c] [b c a])"
  ==
=|  out=(list tank)
|-  ^+  out
?~  case  [leaf+"ok" out]
=*  c  i.case
=/  got=(parm uexp)
    =/  red  (read-tape /test t.c)
    ?>  ?=(%& -.red)
    (parse-uexp:pe p.red)
?.  ?=(%& -.got)  (dump p.got)
?.  =(p.got exp.c)
  :_  out
  :~  %rose  [" " "!{name.c} " ""]
      (sell !>(exp.c))
      (sell !>(p.got))
  ==
$(case t.case, out :_(out leaf+"{name.c} ok"))
