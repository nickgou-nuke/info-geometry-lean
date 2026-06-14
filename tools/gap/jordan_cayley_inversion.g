# GAP finite shadow witnesses for Jordan--Cayley inversion identities.
# Lean owns the rational-coordinate proofs.

F := GF(5);;
AddCs := function(x,y) return [x[1]+y[1], x[2]+y[2]]; end;;
NegCs := function(x) return [-x[1], -x[2]]; end;;
MulCs := function(x,y) return [x[1]*y[1]+x[2]*y[2], x[1]*y[2]+x[2]*y[1]]; end;;
ScalarCs := function(t) return [t, Zero(F)]; end;;
NormCs := function(x) return x[1]^2 - x[2]^2; end;;
ScaleHerm := function(t,X) return [t*X[1], t*X[2], MulCs(ScalarCs(t), X[3])]; end;;
TrRev := function(X) return [X[2], X[1], NegCs(X[3])]; end;;
DetHerm := function(X) return X[1]*X[2] - NormCs(X[3]); end;;

# Planar line-to-circle numerator over GF(5), away from poles.
for A in F do for B in F do for C in F do for u in F do for v in F do
  den := u^2 + v^2;;
  if den <> Zero(F) then
    lhs := den * (A * (u / den) + B * ((-v) / den) + C);;
    rhs := C * (u^2 + v^2) + A*u - B*v;;
    if lhs <> rhs then Error("planar line-to-circle numerator failed"); fi;
  fi;
od; od; od; od; od;

for xp in F do for xm in F do for ar in F do for ai in F do for r in F do
  Xmat := [xp, xm, [ar, ai]];;
  if TrRev(TrRev(Xmat)) <> Xmat then Error("trace reversal involution failed"); fi;
  if DetHerm(TrRev(Xmat)) <> DetHerm(Xmat) then Error("det trace reversal failed"); fi;
  if DetHerm(ScaleHerm(r, Xmat)) <> r^2 * DetHerm(Xmat) then Error("det scale failed"); fi;
  d := DetHerm(Xmat);;
  if d <> Zero(F) then
    Wmat := ScaleHerm(One(F) / d, TrRev(Xmat));;
    if DetHerm(Wmat) <> One(F) / d then Error("det inversion failed"); fi;
    if ScaleHerm(One(F) / DetHerm(Wmat), TrRev(Wmat)) <> Xmat then Error("inversion involution failed"); fi;
  fi;
od; od; od; od; od;

Print("GAP_JORDAN_CAYLEY_GF5_PLANAR_LINE_TO_CIRCLE_OK\n");
Print("GAP_JORDAN_CAYLEY_GF5_CS_TRREV_INVOLUTIVE_OK\n");
Print("GAP_JORDAN_CAYLEY_GF5_CS_DET_TRREV_OK\n");
Print("GAP_JORDAN_CAYLEY_GF5_CS_DET_SCALE_OK\n");
Print("GAP_JORDAN_CAYLEY_GF5_CS_DET_INVERSION_OK\n");
Print("GAP_JORDAN_CAYLEY_GF5_CS_INVERSION_INVOLUTIVE_OK\n");
QUIT;
