BNames := ["E11","E22","U1","U2","U3","V1","V2","V3"];;
Expected := [["E11","0","U1","U2","U3","0","0","0"],["0","E22","0","0","0","V1","V2","V3"],["0","U1","0","V3","-V2","E11","0","0"],["0","U2","-V3","0","V1","0","E11","0"],["0","U3","V2","-V1","0","0","0","E11"],["V1","0","E22","0","0","0","-U3","U2"],["V2","0","0","E22","0","U3","0","-U1"],["V3","0","0","0","E22","-U2","U1","0"]];;
BCell := function(name)
  if name="E11" then return [1,0,0,0,0,0,0,0]; fi;
  if name="E22" then return [0,1,0,0,0,0,0,0]; fi;
  if name="U1" then return [0,0,1,0,0,0,0,0]; fi;
  if name="U2" then return [0,0,0,1,0,0,0,0]; fi;
  if name="U3" then return [0,0,0,0,1,0,0,0]; fi;
  if name="V1" then return [0,0,0,0,0,1,0,0]; fi;
  if name="V2" then return [0,0,0,0,0,0,1,0]; fi;
  if name="V3" then return [0,0,0,0,0,0,0,1]; fi;
end;;
BNeg := c -> List(c, x -> -x);;
BExpr := function(c)
  local i;
  if c=[0,0,0,0,0,0,0,0] then return "0"; fi;
  for i in [1..Length(BNames)] do
    if c=BCell(BNames[i]) then return BNames[i]; fi;
    if c=BNeg(BCell(BNames[i])) then return Concatenation("-",BNames[i]); fi;
  od;
  Error("unknown cell");
end;;
BMul := function(X,Y)
  local r,s,x1,x2,x3,y1,y2,y3,R,S,u1,u2,u3,v1,v2,v3;
  r:=X[1]; s:=X[2]; x1:=X[3]; x2:=X[4]; x3:=X[5]; y1:=X[6]; y2:=X[7]; y3:=X[8];
  R:=Y[1]; S:=Y[2]; u1:=Y[3]; u2:=Y[4]; u3:=Y[5]; v1:=Y[6]; v2:=Y[7]; v3:=Y[8];
  return [r*R+x1*v1+x2*v2+x3*v3, y1*u1+y2*u2+y3*u3+s*S,
    r*u1+S*x1-(y2*v3-y3*v2), r*u2+S*x2-(y3*v1-y1*v3), r*u3+S*x3-(y1*v2-y2*v1),
    R*y1+s*v1+(x2*u3-x3*u2), R*y2+s*v2+(x3*u1-x1*u3), R*y3+s*v3+(x1*u2-x2*u1)];
end;;
for i in [1..8] do for j in [1..8] do
  if BExpr(BMul(BCell(BNames[i]),BCell(BNames[j]))) <> Expected[i][j] then Error("table mismatch"); fi;
od; od;
Print("GAP_ZORN_BASIS_TABLE_OK entries=64\n");
QUIT;
