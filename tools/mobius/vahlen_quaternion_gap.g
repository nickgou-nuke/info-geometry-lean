QMul := function(a, b)
  return [
    a[1]*b[1] - a[2]*b[2] - a[3]*b[3] - a[4]*b[4],
    a[1]*b[2] + a[2]*b[1] + a[3]*b[4] - a[4]*b[3],
    a[1]*b[3] - a[2]*b[4] + a[3]*b[1] + a[4]*b[2],
    a[1]*b[4] + a[2]*b[3] - a[3]*b[2] + a[4]*b[1]
  ];
end;

QAdd := function(a, b)
  return [a[1]+b[1], a[2]+b[2], a[3]+b[3], a[4]+b[4]];
end;

QNeg := a -> [-a[1], -a[2], -a[3], -a[4]];
QConj := a -> [a[1], -a[2], -a[3], -a[4]];
QNorm := a -> a[1]^2 + a[2]^2 + a[3]^2 + a[4]^2;
QInv := function(a)
  local n, c;
  n := QNorm(a);
  c := QConj(a);
  return [c[1]/n, c[2]/n, c[3]/n, c[4]/n];
end;

VahlenAction := function(a, b, c, d, q)
  local num, den;
  num := QAdd(QMul(a, q), b);
  den := QAdd(QMul(c, q), d);
  return QMul(num, QInv(den));
end;

ScalarPacket := function()
  local one, zero, two, half, q, image, recovered;
  one := [1,0,0,0];; zero := [0,0,0,0];; two := [2,0,0,0];; half := [1/2,0,0,0];;
  q := [1,2,3,4];;
  image := VahlenAction(two, zero, zero, one, q);;
  recovered := VahlenAction(half, zero, zero, one, image);;
  if recovered <> q then Error("scalar recovery failed"); fi;
  Print("scalar image = ", image, " recovered = ", recovered, "\n");
end;

NoncommPacket := function()
  local one, zero, i, j, q, aInv, bInv, image, recovered, ij, ji;
  one := [1,0,0,0];; zero := [0,0,0,0];; i := [0,1,0,0];; j := [0,0,1,0];;
  q := [1,2,3,4];;
  aInv := QInv(i);;
  bInv := QNeg(QMul(aInv, j));;
  image := VahlenAction(i, j, zero, one, q);;
  recovered := VahlenAction(aInv, bInv, zero, one, image);;
  ij := QMul(i, j);;
  ji := QMul(j, i);;
  if recovered <> q then Error("noncomm recovery failed"); fi;
  if ij = ji then Error("coefficients should not commute"); fi;
  Print("noncomm image = ", image, " recovered = ", recovered, "\n");
  Print("i*j = ", ij, " ; j*i = ", ji, "\n");
end;

ScalarPacket();;
NoncommPacket();;
Print("VAHLEN_GAP_OK\n");
QUIT;
