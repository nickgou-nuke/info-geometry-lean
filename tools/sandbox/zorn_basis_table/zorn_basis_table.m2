bnames={"E11","E22","U1","U2","U3","V1","V2","V3"};
expected={{"E11","0","U1","U2","U3","0","0","0"},{"0","E22","0","0","0","V1","V2","V3"},{"0","U1","0","V3","-V2","E11","0","0"},{"0","U2","-V3","0","V1","0","E11","0"},{"0","U3","V2","-V1","0","0","0","E11"},{"V1","0","E22","0","0","0","-U3","U2"},{"V2","0","0","E22","0","U3","0","-U1"},{"V3","0","0","0","E22","-U2","U1","0"}};
cell=name -> if name=="E11" then {1,0,0,0,0,0,0,0} else if name=="E22" then {0,1,0,0,0,0,0,0} else if name=="U1" then {0,0,1,0,0,0,0,0} else if name=="U2" then {0,0,0,1,0,0,0,0} else if name=="U3" then {0,0,0,0,1,0,0,0} else if name=="V1" then {0,0,0,0,0,1,0,0} else if name=="V2" then {0,0,0,0,0,0,1,0} else {0,0,0,0,0,0,0,1};
neg=X -> apply(X, x -> -x);
expr=X -> (if X=={0,0,0,0,0,0,0,0} then "0" else (for b in bnames do (if X==cell b then return b; if X==neg cell b then return concatenate("-",b)); error "unknown cell"));
mul=(X,Y) -> (r:=X#0; s:=X#1; x1:=X#2; x2:=X#3; x3:=X#4; y1:=X#5; y2:=X#6; y3:=X#7; R:=Y#0; S:=Y#1; u1:=Y#2; u2:=Y#3; u3:=Y#4; v1:=Y#5; v2:=Y#6; v3:=Y#7; {r*R+x1*v1+x2*v2+x3*v3, y1*u1+y2*u2+y3*u3+s*S, r*u1+S*x1-(y2*v3-y3*v2), r*u2+S*x2-(y3*v1-y1*v3), r*u3+S*x3-(y1*v2-y2*v1), R*y1+s*v1+(x2*u3-x3*u2), R*y2+s*v2+(x3*u1-x1*u3), R*y3+s*v3+(x1*u2-x2*u1)});
for i from 0 to 7 do for j from 0 to 7 do if expr(mul(cell(bnames#i),cell(bnames#j))) != (expected#i)#j then error "table mismatch";
print "MACAULAY2_ZORN_BASIS_TABLE_OK entries=64";
