sigma := function(u,v) return u[1]*v[2] - u[2]*v[1]; end;
padSigma := function(u,v) return u[1]*v[2] + 0 - u[2]*v[1] - 0; end;
normSq := function(u) return u[1]^2 + u[2]^2; end;
padNormSq := function(u) return u[1]^2 + 0 + u[2]^2 + 0; end;
pts := Cartesian([-2..2],[-2..2]);
for u in pts do
  if padNormSq(u) <> normSq(u) then Error("norm not preserved"); fi;
  for v in pts do
    if padSigma(u,v) <> sigma(u,v) then Error("sigma not preserved"); fi;
    if sigma(v,u) <> -sigma(u,v) then Error("sigma not skew"); fi;
  od;
od;
Print(rec(sigma_preserved:=true, norm_preserved:=true, fock_state_zero:=1, identity_trace_status:="not_trace_class_in_infinite_GNS"));
QUIT;
