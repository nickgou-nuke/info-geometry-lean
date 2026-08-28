# Exact rational matrix evidence for a contact 5-grading.
# This is a CAS certificate generator, not a Lean axiom.

Print("SPLIT_CONTACT_FIVE_GRADE_GAP\n");
m := 2;;
n := 2*m + 2;;
F := Rationals;;
zeroMat := NullMat(n,n,F);;
weights := [-2,-1,-1,-1,-1,2];;
J := NullMat(n,n,F);;
for i in [1..QuoInt(n,2)] do
  J[i][n+1-i] := 1;
  J[n+1-i][i] := -1;
od;
H := DiagonalMat(weights,F);;

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
    E := NullMat(n,n,F);;
    E[i][j] := 1;
    X := E-J*TransposedMat(E)*J;
    if X <> zeroMat and ForAny(B,Y -> Y=X)=false then Add(B,X); fi;
  od;
od;

G := [];;
for k in [-4..4] do G[k+5] := Filtered(B,X -> degree(X)=k); od;

closure := true;;
for X in B do for Y in B do
  C := bracket(X,Y);
  if C<>zeroMat and degree(C)=fail then closure := false; fi;
od; od;

jacobi := true;;
for X in B do for Y in B do for W in B do
  if bracket(X,bracket(Y,W))+bracket(Y,bracket(W,X))+
      bracket(W,bracket(X,Y))<>zeroMat then jacobi := false; fi;
od; od; od;

Print("field=QQ\n");
Print("sp_dimension=",Length(B),"\n");
Print("grade_dimensions=");
for k in [-2..2] do Print(k,":",Length(G[k+5])," "); od;
Print("\n");
Print("grade_closure=",closure,"\n");
Print("jacobi=",jacobi,"\n");
Print("certificate=",closure and jacobi,"\n");
