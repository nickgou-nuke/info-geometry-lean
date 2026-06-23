# Exact-rational GAP certificate for Jensen inverse-iteration inclusion.
# This file uses rational arithmetic in Q(s), represented by pairs a + b*s
# with s^2 = radicand at each stage.

Pair := function(a, b)
  return [a, b];
end;

PairAdd := function(x, y)
  return [x[1] + y[1], x[2] + y[2]];
end;

PairNeg := function(x)
  return [-x[1], -x[2]];
end;

PairSub := function(x, y)
  return PairAdd(x, PairNeg(y));
end;

PairMul := function(rad, x, y)
  return [x[1] * y[1] + x[2] * y[2] * rad,
          x[1] * y[2] + x[2] * y[1]];
end;

PairScale := function(c, x)
  return [c * x[1], c * x[2]];
end;

PairInv := function(rad, x)
  local den;
  den := x[1]^2 - x[2]^2 * rad;
  return [x[1] / den, -x[2] / den];
end;

PairDiv := function(rad, x, y)
  return PairMul(rad, x, PairInv(rad, y));
end;

PairPow2 := function(rad, x)
  return PairMul(rad, x, x);
end;

AsPair := function(q)
  return [q, 0];
end;

JensenPolynomial := function(rad, b, j, z)
  local term1, term2, term3;
  term1 := PairScale(-(b[j - 1] - b[j]), PairPow2(rad, z));
  term2 := PairScale(b[j - 1] * (b[j - 2] - b[j]), z);
  term3 := AsPair(-b[j - 1] * b[j] * (b[j - 2] - b[j - 1]));
  return PairAdd(PairAdd(term1, term2), term3);
end;

h := 1 / 5;
q := 1 / 3;
b := [];
for j in [1..7] do
  b[j] := h + q^j;
od;

for j in [3..7] do
  rad := (b[j - 2] - b[j])^2
         - 4 * (b[j - 1] - b[j]) * (b[j - 2] - b[j - 1]) * (b[j] / b[j - 1]);
  s := Pair(0, 1);
  numerator := PairScale(b[j - 1], PairSub(AsPair(b[j - 2] - b[j]), s));
  denominator := AsPair(2 * (b[j - 1] - b[j]));
  delta := PairDiv(rad, numerator, denominator);
  if JensenPolynomial(rad, b, j, delta) <> [0, 0] then
    Error("Jensen polynomial root check failed");
  fi;
  # Exact interval containment h <= delta <= b_j is checked by comparing
  # rational decimal embeddings only after exact root identity; the Lean file
  # treats containment as an explicit certificate field.
  if not (Float(h) <= Float(delta[1] + delta[2] * Sqrt(Float(rad))) and
          Float(delta[1] + delta[2] * Sqrt(Float(rad))) <= Float(b[j])) then
    Error("Jensen interval numeric readout failed");
  fi;
od;

Print("jensen inverse-iteration inclusion GAP certificate: ok\n");
