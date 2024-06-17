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
    :-  %.y
    :~
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
%ok
