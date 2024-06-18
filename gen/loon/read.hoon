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
  =/  r  (read-tape in)
  ?:  ?=(%& -.r)  p.r
  ?:  ?=(%& +<.r)  (pretty-toke-err p.p.r)
  (pretty-read-err p.p.r)
?>  .=  (read-tape "(foo bar baz)")
    :-  %.y
    :-  [[1 1] 1 13]
    :~  %rond
      [[[1 2] [1 4]] [%symb 'foo']]
      [[[1 6] [1 8]] [%symb 'bar']]
      [[[1 10] [1 12]] [%symb 'baz']]
    ==
?>  .=  (read-tape "(1 2 3)")
    :-  %.y
    :-  [[1 1] 1 7]
    :~  %rond
      [[[1 2] [1 2]] 1]
      [[[1 4] [1 4]] 2]
      [[[1 6] [1 6]] 3]
    ==
?>  .=  (read-tape "[1 2 3]")
    :-  %.y
    :-  [[1 1] 1 7]
    :~  %sqar
      [[[1 2] [1 2]] 1]
      [[[1 4] [1 4]] 2]
      [[[1 6] [1 6]] 3]
    ==
?>  .=  (read-tape "[1 () 3]")
    :-  %.y
    :-  [[1 1] 1 8]
    :~  %sqar
      [[[1 2] [1 2]] 1]
      [[[1 4] [1 5]] rond+~]
      [[[1 7] [1 7]] 3]
    ==
?>  .=  (read-tape "")
    |+|+%none
?>  .=  (read-tape "1 2")
    |+|+%many
?>  .=  (read-tape "(1")
    |+|+pope+[1 1]
?>  .=  (read-tape "[1")
    |+|+bope+[1 1]
?>  .=  (read-tape "(1))")
    |+|+clop+[1 4]
?>  .=  (read-tape "[1]]")
    |+|+clob+[1 4]
?>  .=  (read-tape "(1]")
    |+|+cpwb+[[1 1] 1 3]
?>  .=  (read-tape "[1)")
    |+|+cbwp+[[1 1] 1 3]
%ok
