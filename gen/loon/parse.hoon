/+  loon-parse, loon-read
=,  loon-parse
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
?^  in
  =/  par  (parse-tape ~ in)
  ?:  ?=(%& -.par)  ~[leaf+"{<p.par>}"]
  ?:  ?=(%& -.p.par)  ~[leaf+(pretty-read-tape-err p.p.par)]
  =*  err  p.p.par
  :-  ?~  des.err  leaf+"parse error"
      leaf+"{<des.err>}"
  =|  out=(list tank)
  =/  in  tac.err
  |-  ^+  out
  ?~  in  (flop out)
  %=  $  in  t.in  out  :_  out
    :~  %rose  ["|" "" ""]
        leaf+"{<mot.i.in>}"
        ?~  loc.i.in
          leaf+"<no location>"
        (rend-spot loc.i.in)
    ==
  ==
~[leaf+"ok"]
