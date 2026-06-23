# GAP witness for the concrete nonzero square-zero Zorn null mode over Q.
DetZ := function(Z)
  return Z[1]*Z[2] - (Z[3]*Z[6] + Z[4]*Z[7] + Z[5]*Z[8]);
end;

MulZ := function(X,Y)
  return [
    X[1]*Y[1] + (X[3]*Y[6] + X[4]*Y[7] + X[5]*Y[8]),
    (X[6]*Y[3] + X[7]*Y[4] + X[8]*Y[5]) + X[2]*Y[2],
    X[1]*Y[3] + Y[2]*X[3] - (X[7]*Y[8] - X[8]*Y[7]),
    X[1]*Y[4] + Y[2]*X[4] - (X[8]*Y[6] - X[6]*Y[8]),
    X[1]*Y[5] + Y[2]*X[5] - (X[6]*Y[7] - X[7]*Y[6]),
    Y[1]*X[6] + X[2]*Y[6] + (X[4]*Y[5] - X[5]*Y[4]),
    Y[1]*X[7] + X[2]*Y[7] + (X[5]*Y[3] - X[3]*Y[5]),
    Y[1]*X[8] + X[2]*Y[8] + (X[3]*Y[4] - X[4]*Y[3])
  ];
end;

n := [0,0,1,0,0,0,0,0];;
z := [0,0,0,0,0,0,0,0];;
if not (DetZ(n) = 0 and n <> z and MulZ(n,n) = z) then
  Error("split Zorn null witness failed");
fi;
Print("split_zorn_null_boundary.gap: checks passed\n");
