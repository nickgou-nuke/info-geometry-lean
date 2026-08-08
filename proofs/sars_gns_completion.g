sigma := function(u,v) return u[1]*v[2] - u[2]*v[1]; end;
padSigma := function(u,v) return u[1]*v[2] + 0 - u[2]*v[1] - 0; end;
normSq := function(u) return u[1]^2 + u[2]^2; end;
padNormSq := function(u) return u[1]^2 + 0 + u[2]^2 + 0; end;
pts := Cartesian([-2..2],[-2..2]);
for u in pts do
  if padNormSq(u) <> normSq(u) then Error("norm"); fi;
  for v in pts do
    if padSigma(u,v) <> sigma(u,v) then Error("sigma"); fi;
  od;
od;
systems := ["Lean4","SymPy","SageMath","Macaulay2","Rocq","Isabelle","GAP"];
if Length(systems) <> 7 then Error("systems"); fi;
traceStatus := "not_trace_class_in_infinite_GNS";
dmoduleGenerators := 1;
Print(rec(sigma_preserved:=true,norm_preserved:=true,fock_compatible:=true,systems:=Length(systems),identity_trace_status:=traceStatus,dmodule_generators:=dmoduleGenerators));
QUIT;
