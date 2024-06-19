^?
|%
+$  sloc  [lin=@ col=@]
+$  rang  [beg=sloc end=sloc]
+$  deli  $?(%'(' %')' %'[' %']')
+$  toad  $%  [%atom @]
              [%symb @t]
              [%tape tape]
              [%cord cord]
          ==
+$  toke  $^  [ran=rang dat=toad]
          [c=deli loc=sloc]
+$  toke-err  [chr=@tD loc=sloc]
--
