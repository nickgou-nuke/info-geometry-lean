# GAP polynomial verifier for Zorn determinant ratio / scalar-flow identities.
# Universal check over the rational polynomial ring via GAP indeterminates.

MakeZ := function(a, u, v, b) return rec(a := a, u := u, v := v, b := b); end;
Dot := function(u, v) return u[1]*v[1] + u[2]*v[2] + u[3]*v[3]; end;
NormZ := function(X) return X.a * X.b - Dot(X.u, X.v); end;
ScaleZ := function(lambda, X)
  return MakeZ(lambda*X.a,
    [lambda*X.u[1], lambda*X.u[2], lambda*X.u[3]],
    [lambda*X.v[1], lambda*X.v[2], lambda*X.v[3]],
    lambda*X.b);
end;
AssertZero := function(name, expr)
  if not IsZero(expr) then Error(Concatenation(name, " failed: ", String(expr))); fi;
  Print("PASS: ", name, "\n");
end;

a := Indeterminate(Rationals, "a");;
b := Indeterminate(Rationals, "b");;
u1 := Indeterminate(Rationals, "u1");;
u2 := Indeterminate(Rationals, "u2");;
u3 := Indeterminate(Rationals, "u3");;
v1 := Indeterminate(Rationals, "v1");;
v2 := Indeterminate(Rationals, "v2");;
v3 := Indeterminate(Rationals, "v3");;
c := Indeterminate(Rationals, "c");;
d := Indeterminate(Rationals, "d");;
x1 := Indeterminate(Rationals, "x1");;
x2 := Indeterminate(Rationals, "x2");;
x3 := Indeterminate(Rationals, "x3");;
y1 := Indeterminate(Rationals, "y1");;
y2 := Indeterminate(Rationals, "y2");;
y3 := Indeterminate(Rationals, "y3");;
r := Indeterminate(Rationals, "r");;
s := Indeterminate(Rationals, "s");;
t := Indeterminate(Rationals, "t");;

X0 := MakeZ(a, [u1,u2,u3], [v1,v2,v3], b);
Y0 := MakeZ(c, [x1,x2,x3], [y1,y2,y3], d);

AssertZero("N(scale_r(X)) = r^2 N(X)", NormZ(ScaleZ(r, X0)) - r^2 * NormZ(X0));
AssertZero("N(scale_r(Y)) = r^2 N(Y)", NormZ(ScaleZ(r, Y0)) - r^2 * NormZ(Y0));
AssertZero("common-scaling RN numerator after clearing denominators", NormZ(ScaleZ(r, Y0))*NormZ(X0) - NormZ(Y0)*NormZ(ScaleZ(r, X0)));
AssertZero("unequal-scaling RN factor after clearing denominators", s^2*NormZ(ScaleZ(t, Y0))*NormZ(X0) - t^2*NormZ(Y0)*NormZ(ScaleZ(s, X0)));
Print("ZORN_DETERMINANT_RATIO_FLOW_SCALING_OK\n");
QUIT;
