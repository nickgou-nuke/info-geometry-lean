# GAP exact matrix certificate
u := [[0,1],[0,0]];; d := [[0,0],[1,0]];; e := [[1,0],[0,1]];;
Kron := function(A,B)
  local r,c,i,j,C;
  C := NullMat(Length(A)*Length(B),Length(A[1])*Length(B[1]));
  for i in [1..Length(A)] do for j in [1..Length(A[1])] do
    for r in [1..Length(B)] do for c in [1..Length(B[1])] do
      C[(i-1)*Length(B)+r][(j-1)*Length(B[1])+c] := A[i][j]*B[r][c];
    od; od;
  od; od; return C;
end;;
AddM := function(A,B) return A+B; end;;
SubM := function(A,B) return A-B; end;;
Zero4 := NullMat(4,4);; One4 := IdentityMat(4);;
up := Kron(u,e);; dn := Kron(d,e);; sp := Kron(e,u);; sm := Kron(e,d);;
Assert(1,up*up=Zero4 and dn*dn=Zero4 and sp*sp=Zero4 and sm*sm=Zero4);
Assert(1,up*dn+dn*up=One4 and sp*sm+sm*sp=One4);
Assert(1,up*dn-dn*up=DiagonalMat([1,1,-1,-1]));
Assert(1,sp*sm-sm*sp=DiagonalMat([1,-1,1,-1]));
for x in [up,dn] do for y in [sp,sm] do Assert(1,x*y-y*x=Zero4); od; od;
Print("PASS GAP two-sheet closure\n");
