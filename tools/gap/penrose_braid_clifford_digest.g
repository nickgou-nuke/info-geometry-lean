Print("=== GAP Penrose / Artin braid finite quotient digest ===\n");

S3 := SymmetricGroup(3);
s1 := (1,2);
s2 := (2,3);

if s1 * s2 * s1 <> s2 * s1 * s2 then
  Error("S3 Artin relation failed");
fi;
if s1^2 <> () or s2^2 <> () then
  Error("S3 involution quotient failed");
fi;
Print("PASS: S3 Artin quotient relation and involutions\n");

S5 := SymmetricGroup(5);
c5 := (1,2,3,4,5);
if c5^5 <> () or c5 = () then
  Error("5-cycle order check failed");
fi;
Print("PASS: 5-cycle has order five\n");

F := FreeGroup("b1", "b2");
b1 := F.1;
b2 := F.2;
B3S3 := F / [b1*b2*b1*(b2*b1*b2)^-1, b1^2, b2^2];
if Size(B3S3) <> 6 then
  Error("B3 -> S3 quotient size should be 6");
fi;
Print("PASS: finitely presented B3 quotient has order 6\n");

Print("All GAP digest checks passed.\n");
