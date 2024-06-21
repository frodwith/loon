/-  loon-token
=,  loon-token
^?
|%
::  sexp is the user-facing data out of which code is assembled,
::  and the product of the special quote operator.
::  a symbol is evaluated as variable name.
::  an atom evaluates to itself.
::  so, atoms and symbols must be distinguished.
::  a list is evaluated as an operator and argument(s).
::  cells are evaluated as make-a-cell-of-evaluating-my-components.
::  so cells and list structure are also distinguished.
::  cords and tapes preserve intent.
+$  sexp
  $^  [p=sexp q=sexp]        :: brackets
  $%  [%atom a=@]            :: numbers
      [%symb s=@tas]         :: distinguished names
      [%cord c=cord]         :: atomic strings
      [%tape t=tape]         :: listy strings
      [%pair p=sexp q=sexp]  :: list structure (round parens)
      [%null ~]              :: the empty list
  ==
+$  spam  $@(~ spot)
::  lexp is the format produced directly from tokens by the reader,
::  and contains nullable source code ranges (spam).  it is also
::  the format used as input to parse so that it can insert %spot
::  hints, but not the format a loon programmer interacts with
::  when for example quoting a loon expression (see sexp).
::  see "erase" and "nullify" for converting between sexp and lexp.
::  sexp should round trip through lexp, but not vice versa.
::  i think that means they're adjunct.
+$  lexp
  $:  loc=spam
  $=  exp
  $@  @
  $%  [%symb s=@tas]
      [%tape t=tape]
      [%cord c=cord]
      [%rond l=(list lexp)]
      [%sqar i=lexp t=(lest lexp)]  :: at least two lexps
  ==  ==
+$  read-err
  $@  ?(%none %many)         :: wrong number of expressions (not 1)
  $%  [%pope loc=sloc]       :: paren left open
      [%bope loc=sloc]       :: brace left open
      [%bnum n=?(%0 %1) beg=sloc end=sloc]  ::  [<2]
      [%clop loc=sloc]       :: unmatched closing paren
      [%clob loc=sloc]       :: unmatched closing brace
      [%cpwb p=sloc b=sloc]  :: closed paren with brace
      [%cbwp b=sloc p=sloc]  :: vice versa
  ==
+$  read-tape-err  (each toke-err read-err)
--
