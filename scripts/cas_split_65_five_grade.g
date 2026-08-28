# Exact GAP generator for the |2|-grading of split so(6,5).
# No external assertion is trusted: all matrices are over Q.

Print("CAS_SPLIT_SO65_FIVE_GRADE\n");
F := Rationals;;
n := 11;;
zeroMat := NullMat(n,n,F);;
Q := NullMat(n,n,F);;
for i in [1..n] do Q[i][n+1-i] := 1; od;
weights := [-1,-1,0,0,0,0,0,0,0,1,1];;
H := DiagonalMat(weights);;

degree := function(xmat)
  local k;
  for k in [-2..2] do
    if H*xmat-xmat*H=k*xmat then return k; fi;
  od;
  return fail;
end;;
bracket := function(xmat,ymat) return xmat*ymat-ymat*xmat; end;;

B := [];;
for i in [1..n] do for j in [1..n] do
  elem := NullMat(n,n,F);; elem[i][j] := 1;
  xmat := elem-Q*TransposedMat(elem)*Q;
  if xmat<>zeroMat and ForAny(B,zmat -> zmat=xmat)=false then Add(B,xmat); fi;
od; od;
G := [];;
for k in [-2..2] do G[k+3] := Filtered(B,xmat -> degree(xmat)=k); od;
closure := true;;
for xmat in B do for ymat in B do
  cmat := bracket(xmat,ymat);
  if cmat<>zeroMat and degree(cmat)=fail then closure:=false; fi;
od; od;
jacobi := true;;
for xmat in B do for ymat in B do for zmat in B do
  if bracket(xmat,bracket(ymat,zmat))+bracket(ymat,bracket(zmat,xmat))+
      bracket(zmat,bracket(xmat,ymat))<>zeroMat then jacobi:=false; fi;
od; od; od;

Print("gram_size=11x11\n");
Print("gram_rank=",RankMat(Q),"\n");
Print("gram_determinant=",DeterminantMat(Q),"\n");
Print("carrier_dimension=",Length(B),"\n");
Print("grade_dimensions=",List(G,Length),"\n");
Print("dimension_sum=",Sum(G,Length),"\n");
Print("graded_commutator_closure=",closure,"\n");
Print("matrix_jacobi=",jacobi,"\n");
Print("STATUS=",Length(B)=55 and List(G,Length)=[10,5,25,5,10] and
  closure and jacobi,"\n");
