/-  tsur=loon-token, rsur=loon-read
/+  tlib=loon-token, rlib=loon-read
=,  rsur
=,  rlib
=,  tsur
=,  tlib
:-  %say
|=  [^ ~ [in=tape ~]]
:-  %noun
?^  in
  =/  r  (read-tape ~ in)
  ?:  ?=(%& -.r)    p.r
  (pretty-read-tape-err p.r)
?>  .=  (read-tape ~ "(foo bar baz)")
    :-  %0
    :-  `[[1 1] 1 13]
    :~  %rond
      [`[[1 2] [1 4]] [%symb 'foo']]
      [`[[1 6] [1 8]] [%symb 'bar']]
      [`[[1 10] [1 12]] [%symb 'baz']]
    ==
?>  .=  (read-tape ~ "(1 2 3)")
    :-  %0
    :-  `[[1 1] 1 7]
    :~  %rond
      [`[[1 2] [1 2]] 1]
      [`[[1 4] [1 4]] 2]
      [`[[1 6] [1 6]] 3]
    ==
?>  .=  (read-tape ~ "[1 2 3]")
    :-  %0
    :-  `[[1 1] 1 7]
    :~  %sqar
      [`[[1 2] [1 2]] 1]
      [`[[1 4] [1 4]] 2]
      [`[[1 6] [1 6]] 3]
    ==
?>  .=  (read-tape ~ "[1 () 3]")
    :-  %0
    :-  `[[1 1] 1 8]
    :~  %sqar
      [`[[1 2] [1 2]] 1]
      [`[[1 4] [1 5]] rond+~]
      [`[[1 7] [1 7]] 3]
    ==
?>  .=  (read-tape ~ "")
    |+|+%none
?>  .=  (read-tape ~ "1 2")
    |+|+%many
?>  .=  (read-tape ~ "(1")
    |+|+pope+[1 1]
?>  .=  (read-tape ~ "[1")
    |+|+bope+[1 1]
?>  .=  (read-tape ~ "[]")
    |+|+bnum+0+[[1 1] 1 2]
?>  .=  (read-tape ~ "[1]")
    |+|+bnum+1+[[1 1] 1 3]
?>  .=  (read-tape ~ "(1))")
    |+|+clop+[1 4]
?>  .=  (read-tape ~ "[1 2]]")
    |+|+clob+[1 6]
?>  .=  (read-tape ~ "(1]")
    |+|+cpwb+[[1 1] 1 3]
?>  .=  (read-tape ~ "[1)")
    |+|+cbwp+[[1 1] 1 3]
?>  .=  (nullify %pair symb+%foo %pair symb+%bar %null ~)
    `[%rond `symb+%foo `symb+%bar ~]
=/  red  (read-tape ~ "[a (b) c]")
?>  ?=(%& -.red)
=/  ras  (erase p.red)
?>  .=  ras
  :-  [%symb %a]
  :-  [%pair [%symb %b] %null ~]
  [%symb %c]
=/  nul  (nullify ras)
?<  ?=(~ nul)
?>  =(ras (erase nul))
%ok
