#! /usr/bin/env gap
# Exact rational contact five-grading certificate for so(6,5,Q).
m := 5; N := 2 * m + 1;
bad := false;
G := NullMat(N,N,Rationals);
for i in [1..m] do G[i][N-i+1] := 1; G[N-i+1][i] := 1; od;
G[m+1][m+1] := 1;
weights := Concatenation(List([1..m],i -> -1),[0],List([1..m],i -> 1));

conditionMatrix := function()
  local rows,row,r,c,k,v;
  rows := [];
  for r in [1..N] do for c in [1..N] do
    row := List([1..N*N],k -> 0);
    for k in [1..N] do
      v := G[k][c]; if v <> 0 then row[(k-1)*N+r] := row[(k-1)*N+r]+v; fi;
    od;
    for k in [1..N] do
      v := G[r][k]; if v <> 0 then row[(k-1)*N+c] := row[(k-1)*N+c]+v; fi;
    od;
    Add(rows,row);
  od; od;
  return Matrix(Rationals,rows);
end;

constraint := conditionMatrix();
nullspace := NullspaceMat(constraint);
vectorToMatrix := function(v)
  local X,r,c; X := NullMat(N,N,Rationals);
  for r in [1..N] do for c in [1..N] do X[r][c] := v[(r-1)*N+c]; od; od;
  return X;
end;
gradeOf := function(X)
  local r,c,g,found; found := fail;
  for r in [1..N] do for c in [1..N] do if X[r][c] <> 0 then
    g := weights[r]-weights[c];
    if found=fail then found:=g; elif found<>g then return fail; fi;
  fi; od; od;
  if found=fail then return 0; fi; return found;
end;
gradeBasis := function(g)
  local cols,rows,r,c,k,restricted,out,v,X;
  cols := [];
  for r in [1..N] do for c in [1..N] do
    if weights[r]-weights[c]=g then Add(cols,(r-1)*N+c); fi;
  od; od;
  rows := [];
  for r in [1..N] do for c in [1..N] do
    Add(rows,List(cols,k -> constraint[(r-1)*N+c][k]));
  od; od;
  restricted := NullspaceMat(TransposedMat(Matrix(Rationals,rows))); out := [];
  for k in [1..NumberRows(restricted)] do
    v := restricted[k];
    X := NullMat(N,N,Rationals);
    for r in [1..Length(cols)] do
      c := QuoInt(cols[r]-1,N)+1;
      X[c][RemInt(cols[r]-1,N)+1] := v[r];
    od;
    Add(out,X);
  od;
  return out;
end;
comm := function(a,b) return a*b-b*a; end;
allBasis := List(nullspace,vectorToMatrix);
grades := [-2,-1,0,1,2];
gradeBases := List(grades,gradeBasis);
gradeDims := List(gradeBases,Length);
zero := NullMat(N,N,Rationals);

if RankMat(G) <> N then
  bad := true;
fi;
if Length(allBasis) <> 55 then
  bad := true;
fi;
if gradeDims <> [10,5,25,5,10] then
  bad := true;
fi;

for i in [1..Length(grades)] do for j in [1..Length(grades)] do
  for a in gradeBases[i] do for b in gradeBases[j] do
    c := comm(a,b);
    if c <> zero then
      if grades[i]+grades[j] < -2 or grades[i]+grades[j] > 2 then
        bad := true;
      fi;
      if gradeOf(c) <> grades[i]+grades[j] then
        bad := true;
      fi;
    fi;
  od; od;
od; od;

if bad then
  Print("SPLIT_CONTACT_SO65_FIVE_GRADE_EVIDENCE\n");
  Print("STATUS=FAIL\n");
else
Print("SPLIT_CONTACT_SO65_FIVE_GRADE_EVIDENCE\n");
Print("algebra=so(6,5,Q)\n");
Print("quadratic_form_rank=",RankMat(G),"\n");
Print("carrier_dimension=",Length(allBasis),"\n");
Print("grade_labels=",grades,"\n");
Print("grade_dimensions=",gradeDims,"\n");
Print("dimension_sum=",Sum(gradeDims),"\n");
Print("graded_commutator_closure=verified\n");
Print("matrix_jacobi=structural_from_associativity\n");
Print("STATUS=PASS\n");
fi;
