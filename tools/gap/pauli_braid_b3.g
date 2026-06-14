# GAP exact witness for the finite Pauli B3 braid identity.

RequireTrue := function(label, cond)
  if not cond then Error(Concatenation(label, " failed")); fi;
  Print(label, " OK\n");
end;

I := E(4);
one := [[1,0],[0,1]];
s1 := [[0,1],[1,0]];
s2 := [[0,-I],[I,0]];
s3 := [[1,0],[0,-1]];
A := one + I * s1;
B := one + I * s2;

RequireTrue("GAP_PAULI_B3_SQUARES_1", s1 * s1 = one);
RequireTrue("GAP_PAULI_B3_SQUARES_2", s2 * s2 = one);
RequireTrue("GAP_PAULI_B3_SQUARES_3", s3 * s3 = one);
RequireTrue("GAP_PAULI_B3_ANTICOMM", s1 * s2 = -s2 * s1);
RequireTrue("GAP_PAULI_B3_SIGMA12", s1 * s2 = I * s3);
RequireTrue("GAP_PAULI_B3_BRAID", A * B * A = B * A * B);
RequireTrue("GAP_PAULI_B3_TRIPLE_PRODUCT", A * B * A = 2 * I * (s1 + s2));
Print("GAP_PAULI_B3_PACKET_OK\n");
