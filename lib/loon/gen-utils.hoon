|%
+$  input  $@(~ [p=path t=tape])
++  sing
  |=  t=tang
  ~>  %slog.[0 %rose [[10 ~] "" ""] (flop t)]
  ~
++  rant
  |=  t=tape
  ~>  %slog.[0 leaf+t]
  ~
++  gen-input
  |=  [p=path t=tape]
  ^-  input
  ?^  t  `t
  ?~  p  ~
  =/  file  .^(mime %cx p)
  [p (trip (end [3 p.q.file] q.q.file))]
--
