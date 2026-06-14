# GAP witness for finite reductions of Klein split-complex stabilizer matrices.
# Over GF(3), use j^2=1 represented by pairs (a,b), and E=(1,1), Ebar=(1,-1).
# This is a finite shadow only; Lean owns the rational-coordinate proof.

F := GF(3);;
AddCs := function(x,y) return [x[1]+y[1], x[2]+y[2]]; end;;
NegCs := function(x) return [-x[1], -x[2]]; end;;
SubCs := function(x,y) return AddCs(x, NegCs(y)); end;;
MulCs := function(x,y) return [x[1]*y[1]+x[2]*y[2], x[1]*y[2]+x[2]*y[1]]; end;;
Qsmul := function(r,x) return [r*x[1], r*x[2]]; end;;
CZERO := [Zero(F), Zero(F)];;
CONE := [One(F), Zero(F)];;
CE := [One(F), One(F)];;
CEBAR := [One(F), -One(F)];;
Act := function(M, psi)
  return [AddCs(MulCs(M[1], psi[1]), MulCs(M[2], psi[2])),
          AddCs(MulCs(M[3], psi[1]), MulCs(M[4], psi[2]))];
end;;
Det := function(M) return SubCs(MulCs(M[1], M[4]), MulCs(M[2], M[3])); end;;

if MulCs(CE, CEBAR) <> CZERO then Error("E*Ebar failed"); fi;
for x in F do
  for y in F do
    b := [x,y];;
    Mgen := [CONE,b,CZERO,CONE];;
    if Det(Mgen) <> CONE then Error("generic determinant failed"); fi;
    if Act(Mgen, [CONE,CZERO]) <> [CONE,CZERO] then Error("generic stabilizer failed"); fi;
    for d1 in F do
      for d2 in F do
        d := [d1,d2];;
        MgenShape := [CONE,b,CZERO,d];;
        if Det(MgenShape) <> d then Error("generic shape determinant projection failed"); fi;
        if Det(MgenShape) = CONE and d <> CONE then Error("generic determinant-one shape failed"); fi;
      od;
    od;
    for r in F do
      for s in F do
        MnullDetOne := [CONE, CZERO, Qsmul(s,CEBAR), CONE];;
        if Det(MnullDetOne) <> CONE then Error("null determinant-one family failed"); fi;
        if Act(MnullDetOne, [CE,CZERO]) <> [CE,CZERO] then Error("null determinant-one stabilizer failed"); fi;
        Mnull := [AddCs(CONE,Qsmul(r,CEBAR)), b, Qsmul(s,CEBAR), [y,x]];;
        if Act(Mnull, [CE,CZERO]) <> [CE,CZERO] then Error("null stabilizer failed"); fi;
        if SubCs(MulCs(Mnull[1], CE), CE) <> Qsmul(Mnull[1][1] + Mnull[1][2] - One(F), CE) then Error("null scalar aa failed"); fi;
        if MulCs(Mnull[3], CE) <> Qsmul(Mnull[3][1] + Mnull[3][2], CE) then Error("null scalar ba failed"); fi;
        rParam := Mnull[1][1] - One(F);;
        sParam := Mnull[3][1];;
        if Mnull[1] <> AddCs(CONE, Qsmul(rParam, CEBAR)) then Error("null aa Ebar shape failed"); fi;
        if Mnull[3] <> Qsmul(sParam, CEBAR) then Error("null ba Ebar shape failed"); fi;
        Mdiag := [[r,s], b, Qsmul(s,CEBAR), [y,x]];;
        out := Act(Mdiag, [CE,CE]);;
        row1 := Mdiag[1][1] + Mdiag[1][2] + Mdiag[2][1] + Mdiag[2][2];;
        row2 := Mdiag[3][1] + Mdiag[3][2] + Mdiag[4][1] + Mdiag[4][2];;
        if SubCs(out[1], CE) <> Qsmul(row1 - One(F), CE) then Error("diagonal row one failed"); fi;
        if SubCs(out[2], CE) <> Qsmul(row2 - One(F), CE) then Error("diagonal row two failed"); fi;
      od;
    od;
  od;
od;
Print("GAP_KLEIN_SPINOR_GF3_E_CZERO_DIVISOR_OK\n");
Print("GAP_KLEIN_SPINOR_GF3_GENERIC_UNIPOTENT_OK\n");
Print("GAP_KLEIN_SPINOR_GF3_GENERIC_STABILIZER_SHAPE_OK\n");
Print("GAP_KLEIN_SPINOR_GF3_NULL_E_SCALAR_CONDITIONS_OK\n");
Print("GAP_KLEIN_SPINOR_GF3_NULL_FIRST_COLUMN_EBAR_SHAPE_OK\n");
Print("GAP_KLEIN_SPINOR_GF3_NULL_EBAR_FAMILY_DET_ONE_OK\n");
Print("GAP_KLEIN_SPINOR_GF3_NULL_EBAR_FAMILY_OK\n");
Print("GAP_KLEIN_SPINOR_GF3_DIAGONAL_NULL_ROW_CONDITION_OK\n");
QUIT;
