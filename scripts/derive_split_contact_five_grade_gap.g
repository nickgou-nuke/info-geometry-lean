# Exact rational matrix evidence for a contact 5-grading.
# This is a CAS certificate generator, not a Lean axiom.

Print("SPLIT_CONTACT_FIVE_GRADE_GAP\n");
m := 5;;
n := 2*m + 2;;
F := Rationals;;
zeroMat := NullMat(n,n,F);;
weights := [-1,0,0,0,0,0,0,0,0,0,0,1];;
J := NullMat(n,n,F);;
for i in [1..QuoInt(n,2)] do
  J[i][n+1-i] := 1;
  J[n+1-i][i] := -1;
od;
H := DiagonalMat(weights);;

symp := function(X)
  return TransposedMat(X)*J + J*X = zeroMat;
end;;
grade := function(X,k)
  return H*X-X*H = k*X;
end;;
degree := function(X)
  local k;
  for k in [-4..4] do
    if grade(X,k) then return k; fi;
  od;
  return fail;
end;;
bracket := function(X,Y) return X*Y-Y*X; end;;

# Elementary generators X - J Xᵀ J span the symplectic Lie algebra.
B := [];;
for i in [1..n] do
  for j in [1..n] do
    elem := NullMat(n,n,F);;
    elem[i][j] := 1;
    xmat := elem-J*TransposedMat(elem)*J;
    if xmat <> zeroMat and ForAny(B,Y -> Y=xmat)=false then Add(B,xmat); fi;
  od;
od;

G := [];;
for k in [-4..4] do G[k+5] := Filtered(B,X -> degree(X)=k); od;

closure := true;;
for x1 in B do for y1 in B do
  C := bracket(x1,y1);
  if C<>zeroMat and degree(C)=fail then closure := false; fi;
od; od;

jacobi := true;;
for x1 in B do for y1 in B do for w1 in B do
  if bracket(x1,bracket(y1,w1))+bracket(y1,bracket(w1,x1))+
      bracket(w1,bracket(x1,y1))<>zeroMat then jacobi := false; fi;
od; od; od;

Print("field=QQ\n");
Print("algebra=sp(12,QQ)\n");
Print("carrier_dimension=",Length(B),"\n");
Print("grade_dimensions=");
for k in [-2..2] do Print(k,":",Length(G[k+5])," "); od;
Print("\n");
Print("grade_closure=",closure,"\n");
Print("jacobi=",jacobi,"\n");
Print("dimension_sum=",Sum([-2..2],k -> Length(G[k+5])),"\n");
Print("cross_extreme_actions=",Length(G[3])=1 and Length(G[7])=1 and
  Length(G[4])=10 and Length(G[6])=10,"\n");
Print("graded_commutator_closure=",closure,"\n");
Print("matrix_jacobi=",jacobi,"\n");
Print("STATUS=",closure and jacobi and Length(B)=78,"\n");
