/-  lsur=loon-token
/+  llib=loon-token
=,  lsur
=,  llib
:-  %say
|=  [^ ~ [in=tape ~]]
:-  %noun
?^  in  (tokenize in)
?>  .=  (tokenize "63")
    &+~[[[[1 1] 1 2] atom+63]]
?>  .=  (tokenize "foo")
    &+~[[[[1 1] 1 3] symb+%foo]]
?>  .=  (tokenize "_")
    &+~[[[[1 1] 1 1] symb+%$]]
?>  .=  (tokenize "\"hello\"")
    &+~[[[[1 1] 1 7] tape+"hello"]]
?>  .=  (tokenize "'hello'")
    &+~[[[[1 1] 1 7] cord+'hello']]
?>  .=  (tokenize "(fn [x y] [y x])")
    :~  %.y
      [%'(' [1 1]]
      [[[1 2] [1 3]] [%symb 'fn']]
      [%'[' [1 5]]
      [[[1 6] [1 6]] [%symb 'x']]
      [[[1 8] [1 8]] [%symb 'y']]
      [%']' [1 9]]
      [%'[' [1 11]]
      [[[1 12] [1 12]] [%symb 'y']]
      [[[1 14] [1 14]] [%symb 'x']]
      [%']' [1 15]]
      [%')' [1 16]]
    ==
?>  .=  %-  tokenize
"""
(foo
  (bar baz
       qux))
"""
    :~  %.y
        [%'(' [1 1]]
        [[[1 2] [1 4]] [%symb 'foo']]
        [%'(' [2 3]]
        [[[2 4] [2 6]] [%symb 'bar']]
        [[[2 8] [2 10]] [%symb 'baz']]
        [[[3 8] [3 10]] [%symb 'qux']]
        [%')' [3 11]]
        [%')' [3 12]]
    ==
?>  .=  [%.n '_' 1 4]
    (tokenize "foo_")
?>  .=  [%.n '3' 1 4]
    (tokenize "foo3")
?>  .=  [%.n 'f' 1 3]
    (tokenize "12f3")
?>  .=  [%.n '$' 1 1]
    (tokenize "$")
%ok
