# Exact GAP certificate for extremal and derivation sectors.
n:=10;; MatUnit:=function(i,j) local A; A:=NullMat(n,n,Rationals); A[i][j]:=1; return A; end;;
B:=function(A,C) return A*C-C*A; end;;
genUp:=MatUnit(10,2);; genSp:=MatUnit(2,1);; genUm:=MatUnit(1,2);; genSm:=MatUnit(2,10);;
genQp:=B(genUp,genSp);; genQm:=B(genUm,genSm);; genD0:=B(genSm,genUp);;
Assert(1,genQp=MatUnit(10,1));; Assert(1,genQm=MatUnit(1,10));;
Assert(1,genD0=MatUnit(2,2)-MatUnit(10,10));;
units:=List([1..n],i->List([1..n],j->MatUnit(i,j)));;
for row in units do for xx in row do for row2 in units do for yy in row2 do
  Assert(1,B(genD0,B(xx,yy))=B(B(genD0,xx),yy)+B(xx,B(genD0,yy)));
od; od; od; od;
Print("PASS GAP two-sheet TKK derivations and five grades\n");
