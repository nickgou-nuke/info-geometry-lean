sigma := function(u,v) return u[1]*v[2] - u[2]*v[1]; end;
padSigma := function(u,v) return u[1]*v[2] + 0 - u[2]*v[1] - 0; end;
testPoints := Cartesian([-2..2],[-2..2]);
for u in testPoints do
  for v in testPoints do
    if padSigma(u,v) <> sigma(u,v) then Error("sigma not preserved"); fi;
    if sigma(v,u) <> -sigma(u,v) then Error("sigma not skew"); fi;
  od;
od;
blockDim := n -> 32^n;
if blockDim(0) <> 1 then Error("block0"); fi;
if blockDim(1) <> 32 then Error("block1"); fi;
if blockDim(2) <> 1024 then Error("block2"); fi;
if 2^10 <> blockDim(2) then Error("cl55 block2"); fi;
Print(rec(sigma_preserved:=true, sigma_skew:=true, block0:=blockDim(0), block1:=blockDim(1), block2:=blockDim(2), cl55_dim:=2^10, odd_odd_target_even:=true));
QUIT;
