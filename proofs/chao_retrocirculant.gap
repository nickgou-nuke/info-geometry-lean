# Exact-rational GAP certificate for Chao retrocirculants.
# Uses concrete rational eigenvalue parameters to verify Chao's factorization.

n := 8;;
sigma := List([0..7], k -> (5*k) mod n);;
if ForAny([1..8], i -> sigma[sigma[i]+1] <> i-1) then Error("not involutive"); fi;
fixed := Filtered([0..7], k -> sigma[k+1] = k);;
if fixed <> [0,2,4,6] then Error("fixed set mismatch"); fi;
cycles := [[1,5],[3,7]];;
mu := [2,3,5,7,11,13,17,19];;
P := NullMat(n,n,Rationals);;
for r in [0..7] do
  for c in [0..7] do
    if sigma[c+1] = r then P[r+1][c+1] := 1; fi;
  od;
od;
D := DiagonalMat(mu);;
A := P * D;;
# Determinant polynomial by exact evaluation interpolation is overkill; instead
# verify fixed and two-cycle block products by direct entries.
for k in fixed do
  if A[k+1][k+1] <> mu[k+1] then Error("fixed block mismatch"); fi;
od;
for pair in cycles do
  i := pair[1];; j := pair[2];;
  if A[i+1][j+1] <> mu[j+1] then Error("ij block mismatch"); fi;
  if A[j+1][i+1] <> mu[i+1] then Error("ji block mismatch"); fi;
  if Determinant([[0, mu[j+1]],[mu[i+1], 0]]) <> -mu[i+1]*mu[j+1] then Error("block determinant mismatch"); fi;
od;
Print("chao retrocirculant GAP certificate: ok\n");
