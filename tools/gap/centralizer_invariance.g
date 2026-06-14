# GAP exact witness for central-sign conjugation.

RequireTrue := function(label, cond)
  if not cond then Error(Concatenation(label, " failed")); fi;
  Print(label, " OK\n");
end;

M := [[2,3],[5,7]];
I2 := [[1,0],[0,1]];
neg := -I2;

RequireTrue("GAP_CENTRALIZER_NEG_ONE_CONJUGATION", neg * M * neg = M);
RequireTrue("GAP_CENTRALIZER_SIGN_FRAME", I2 * M * I2 = M);
Print("GAP_CENTRALIZER_PACKET_OK\n");
