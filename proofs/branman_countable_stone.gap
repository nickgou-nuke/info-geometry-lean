# Exact finite-core check for the Branman countable-Stone layer.
for m in [1..6] do
  if Size(SymmetricGroup(m)) <> Factorial(m) then
    Error("finite permutation count failed");
  fi;
od;

modulus := 5;;
labels := [1, 4];;
Adj := function(g, h) return ((h - g) mod modulus) in labels; end;

for f in labels do
  if not (((-f) mod modulus) in labels) then
    Error("inverse label closure failed");
  fi;
od;

for g in [0..4] do
  for h in [0..4] do
    if Adj(g, h) <> Adj(h, g) then
      Error("adjacency symmetry failed");
    fi;
    for k in [0..4] do
      if Adj(g, h) <> Adj((k + g) mod modulus, (k + h) mod modulus) then
        Error("left translation invariance failed");
      fi;
    od;
  od;
od;

Print("branman countable Stone finite core GAP check: ok\n");
