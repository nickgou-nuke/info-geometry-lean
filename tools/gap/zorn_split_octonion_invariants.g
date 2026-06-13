# GAP exact-rational Zorn split-octonion verifier.

Dot := function(x, y)
  return x[1]*y[1] + x[2]*y[2] + x[3]*y[3];
end;

Cross := function(x, y)
  return [
    x[2]*y[3] - x[3]*y[2],
    x[3]*y[1] - x[1]*y[3],
    x[1]*y[2] - x[2]*y[1]
  ];
end;

ZM := function(a, u, v, b)
  return rec(a := a, u := u, v := v, b := b);
end;

ZAdd := function(X, Y)
  return ZM(X.a + Y.a,
           [X.u[1]+Y.u[1], X.u[2]+Y.u[2], X.u[3]+Y.u[3]],
           [X.v[1]+Y.v[1], X.v[2]+Y.v[2], X.v[3]+Y.v[3]],
           X.b + Y.b);
end;

ZNeg := function(X)
  return ZM(-X.a, [-X.u[1], -X.u[2], -X.u[3]],
                 [-X.v[1], -X.v[2], -X.v[3]], -X.b);
end;

ZSub := function(X, Y)
  return ZAdd(X, ZNeg(Y));
end;

ZScale := function(r, X)
  return ZM(r*X.a, [r*X.u[1], r*X.u[2], r*X.u[3]],
                  [r*X.v[1], r*X.v[2], r*X.v[3]], r*X.b);
end;

ZMul := function(X, Y)
  local c1, c2;
  c1 := Cross(X.v, Y.v);
  c2 := Cross(X.u, Y.u);
  return ZM(X.a*Y.a + Dot(X.u, Y.v),
           [X.a*Y.u[1] + Y.b*X.u[1] - c1[1],
            X.a*Y.u[2] + Y.b*X.u[2] - c1[2],
            X.a*Y.u[3] + Y.b*X.u[3] - c1[3]],
           [Y.a*X.v[1] + X.b*Y.v[1] + c2[1],
            Y.a*X.v[2] + X.b*Y.v[2] + c2[2],
            Y.a*X.v[3] + X.b*Y.v[3] + c2[3]],
           Dot(X.v, Y.u) + X.b*Y.b);
end;

ZTrace := function(X)
  return X.a + X.b;
end;

ZNorm := function(X)
  return X.a*X.b - Dot(X.u, X.v);
end;

ZConj := function(X)
  return ZM(X.b, [-X.u[1], -X.u[2], -X.u[3]],
               [-X.v[1], -X.v[2], -X.v[3]], X.a);
end;

ZScalar := function(r)
  return ZM(r, [0,0,0], [0,0,0], r);
end;

Components := function(X)
  return [X.a, X.u[1], X.u[2], X.u[3], X.v[1], X.v[2], X.v[3], X.b];
end;

IsZeroZ := function(X)
  return ForAll(Components(X), c -> c = 0);
end;

AssertZero := function(name, X)
  if not IsZeroZ(X) then
    Error(Concatenation(name, " failed: ", String(Components(X))));
  fi;
  Print("PASS: ", name, "\n");
end;

AssertNonZero := function(name, X)
  if IsZeroZ(X) then
    Error(Concatenation(name, " unexpectedly vanished"));
  fi;
  Print("PASS: ", name, ": ", Components(X), "\n");
end;

Assoc := function(X, Y, W)
  return ZSub(ZMul(ZMul(X,Y),W), ZMul(X,ZMul(Y,W)));
end;

QuadraticResidual := function(X)
  return ZAdd(ZSub(ZMul(X,X), ZScale(ZTrace(X), X)), ZScalar(ZNorm(X)));
end;

samples := [
  ZM(2, [1,3,-1], [4,0,2], -3),
  ZM(1/2, [0,1,2], [-2,5,1], 7/3),
  ZM(0, [1,0,0], [0,1,0], 0)
];

for sampleElt in samples do
  AssertZero("X + conjugate(X) = Tr(X)1",
    ZSub(ZAdd(sampleElt, ZConj(sampleElt)), ZScalar(ZTrace(sampleElt))));
  AssertZero("X conjugate(X) = N(X)1",
    ZSub(ZMul(sampleElt, ZConj(sampleElt)), ZScalar(ZNorm(sampleElt))));
  AssertZero("quadratic identity", QuadraticResidual(sampleElt));
od;

E1 := ZM(0, [1,0,0], [0,0,0], 0);
E2 := ZM(0, [0,1,0], [0,0,0], 0);
E3 := ZM(0, [0,0,1], [0,0,0], 0);
AssertNonZero("nonassociativity witness", Assoc(E1,E2,E3));
AssertZero("left alternativity witness", Assoc(E1,E1,E2));
AssertZero("right alternativity witness", Assoc(E2,E1,E1));

P := ZM(1, [1,0,0], [0,0,0], 0);
AssertZero("trace-one norm-zero idempotent", ZSub(ZMul(P,P), P));

Q := ZM(0, [1,0,0], [0,0,0], 0);
AssertZero("trace-zero norm-zero nilpotent", ZMul(Q,Q));

Print("All GAP exact-rational Zorn checks passed.\n");
QUIT;
