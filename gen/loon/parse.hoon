/-  psur=loon-parse
/+  plib=loon-parse, loon-read, gut=loon-gen-utils
=,  psur
=,  plib
=,  loon-read
=,  gut
:-  %say
|=  [^ ~ [=path =tape ~]]
:-  %noun
^-  (unit uexp)
=/  in  (gen-input path tape)
?^  in
  =/  par  (parse-tape in)
  ?:  ?=(%| -.par)  (sing (pretty-parse-tape-err p.par))
  `p.par
=/  case=(list [name=^tape exp=uexp t=^tape])
  :~  :+  "number"  litn+12           "12"
      :+  "symbol"  %a                "a"
      :+  "tape"    tape+"hi"         "\"hi\""
      :+  "cord"    cord+'hi'         "'hi'"
      :+  "cell"    [%cons %a %b]     "[a b]"
      :+  "bump"    bump+litn+42      "(+ 42)"
      :+  "deep"    deep+%a           "(? a)"
      :+  "same"    [%same %a %b]     "(= a b)"
      :+  "if"      [%if %a %b %c]    "(if a b c)"
      :+  "with"    [%with [%$ %b] [%frag 3 %c] %b]
      "(with [_ b] (/ 3 c) b)"
      :+  "letn"
        :+  %letn  `[[[%a %$] %c] %appl %foo %bar]
        [%cons %a %c]
      "(let ([[a _] c] (foo bar)) [a c])"
      :+  "letr single"  [%letr [~ %foo %a] %a]  "(rec (foo a) a)"
      :+  "letr multi"
        [%letr [[~ %foo %a] ~ %bar %b] %cons %foo %bar]
      "(rec [(foo a) (bar b)] [foo bar])"
      :+  "bind"  [%bind %d [[%a %b] %c] %cons %b %cons %c %a]
      "(bind d [[a b] c] [b c a])"
      :+  "fn"  [%lamb %$ %a %a]  "(fn a a)"
      :+  "rfn"
        :*  %lamb  %loop  %i
            %if    [%same %i litn+4]
            cord+'done'
            [%appl %loop %bump %i]
        ==
      "(fn loop i (if (= i 4) 'done' (loop (+ i))))"
      :+  "appl"  [%appl %foo %a]           "(foo a)"
      :+  "app2"  [%appl %foo %cons %a %b]  "(foo a b)"
      :+  "aind"  [%appl [%frag 3 %c] %a]   "((/ 3 c) a)"
      :+  "dfn"   [%delt %a %a]             "(dfn a a)"
      :+  "nock"  [%nock %fol %bus]         "(* fol bus)"
      :+  "autonock"  [%nock %fol %cons %hed %tal]
      "(* fol hed tal)"
      :+  "core"  [%core ~ %foo %a]  "(core (foo a))"
      :+  "cor2"  [%core [~ %foo %a] ~ %bar %b]
      "(core [(foo a) (bar b)])"
      :+  "autocore"  [%core [~ %foo %a] ~ %bar %b]
      "(core (foo a) (bar b))"
      :+  "pull"  [%pull 2 %core ~ %foo litn+42]
      "(pull 2 (core (foo 42)))"
      :+  "sint"  [%sint %tag litn+42]  "(sint 'tag' 42)"
      :+  "dint"  [%dint %tag tape+"clu" litn+42]
      "(dint 'tag' \"clu\" 42)"
  ==
=-  (sing -)
=|  out=tang
|-  ^+  out
?~  case  [leaf+"ok" out]
=*  c  i.case
=/  got=(parm uexp)
    =/  red  (read-tape [%test (crip name.c) ~] t.c)
    ?>  ?=(%& -.red)
    (parse-uexp:pe p.red)
?:  ?=(%| -.got)  (pretty-parse-err p.got)
?.  =(p.got exp.c)
  :_  out
  :~  %rose  [" " "!{name.c} " ""]
      (sell !>(exp.c))
      (sell !>(p.got))
  ==
$(case t.case, out :_(out leaf+"{name.c} ok"))
