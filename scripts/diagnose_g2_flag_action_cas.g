F := GF(2);
Print("BEGIN\n");
codes := [
  [2,1,128,64,32,16,8,4],
  [2,1,128,192,224,24,12,4],
  [134,133,128,68,175,211,136,4],
  [1,2,4,8,24,32,192,128],
  [129,130,4,8,147,40,68,128],
  [2,1,64,32,128,8,4,16]
];
gens := List(codes, c -> List([1..8], i ->
  List([1..8], j -> ((Int(c[j] / 2^(i-1)) mod 2) * One(F)))));
Print("GENS\n");
G := Group(gens);
Print("G=", Size(G), "\n");
B := SylowSubgroup(G, 2);
Print("B=", Size(B), "\n");
Q := RightCosets(G, B);
Print("Q=", Length(Q), "\n");
act := ActionHomomorphism(G, Q, OnRight);
A := Image(act);
Print("ACTION\n");
Print("TRANS=", IsTransitive(A), "\n");
Print("STAB=", Size(Stabilizer(A, 1)), "\n");
Print("DONE\n");
QUIT;
