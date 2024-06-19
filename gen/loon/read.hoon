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
  ?-  -.r
    %0  +.r
    %1  (pretty-toke-err +.r)
    %2  (pretty-read-err +.r)
  ==
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
    2+%none
?>  .=  (read-tape ~ "1 2")
    2+%many
?>  .=  (read-tape ~ "(1")
    2+pope+[1 1]
?>  .=  (read-tape ~ "[1")
    2+bope+[1 1]
?>  .=  (read-tape ~ "[]")
    2+bnum+0+[[1 1] 1 2]
?>  .=  (read-tape ~ "[1]")
    2+bnum+1+[[1 1] 1 3]
?>  .=  (read-tape ~ "(1))")
    2+clop+[1 4]
?>  .=  (read-tape ~ "[1 2]]")
    2+clob+[1 6]
?>  .=  (read-tape ~ "(1]")
    2+cpwb+[[1 1] 1 3]
?>  .=  (read-tape ~ "[1)")
    2+cbwp+[[1 1] 1 3]
?>  .=  (nullify %pair symb+%foo %pair symb+%bar %null ~)
    `[%rond `symb+%foo `symb+%bar ~]
=/  red=tred  (read-tape ~ "[a (b) c]")
?>  ?=(%0 -.red)
=/  ras  (erase +.red)
?>  .=  ras
  :-  [%symb %a]
  :-  [%pair [%symb %b] %null ~]
  [%symb %c]
=/  nul  (nullify ras)
?<  ?=(~ nul)
?>  =(ras (erase nul))
%ok
