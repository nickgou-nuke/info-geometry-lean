G := [[1,0,0,0,0],[0,1,0,0,0],[0,0,1,0,0],[0,0,0,0,-2],[0,0,0,-2,0]];
Dot := function(u,v) local i,j,s; s:=0; for i in [1..5] do for j in [1..5] do s:=s+u[i]*G[i][j]*v[j]; od; od; return s; end;
n := [0,0,0,1,0]; nb := [0,0,0,0,1];
if Dot(n,n)<>0 then Error("n"); fi;
if Dot(nb,nb)<>0 then Error("nb"); fi;
if Dot(n,nb)<>-2 then Error("nnb"); fi;
Display("OK");
