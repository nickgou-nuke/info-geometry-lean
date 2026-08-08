CasimirOnShell := m -> -m*m;
StiffnessFromCasimir := C -> -C;
MassStiffness := m -> m*m;
Potential2FromCasimir := function(C,lam) return -C*lam*lam; end;
Potential2Mass := function(m,lam) return m*m*lam*lam; end;
ForceFromCasimir := function(C,lam) return C*lam; end;
ForceMass := function(m,lam) return -m*m*lam; end;
for m in [-5..5] do
  if StiffnessFromCasimir(CasimirOnShell(m)) <> MassStiffness(m) then Error("stiffness"); fi;
  if MassStiffness(m) < 0 then Error("mass nonneg"); fi;
  if Potential2Mass(m,0) <> 0 then Error("vacuum"); fi;
  for lam in [-5..5] do
    if Potential2FromCasimir(CasimirOnShell(m),lam) <> Potential2Mass(m,lam) then Error("potential"); fi;
    if ForceFromCasimir(CasimirOnShell(m),lam) <> ForceMass(m,lam) then Error("force"); fi;
    if Potential2Mass(m,lam) < 0 then Error("potential nonneg"); fi;
  od;
od;
edges := ["labels","identical_to","gives_stiffness","resists","crosses","restores_to"];
if Length(edges) <> 6 then Error("edges"); fi;
Print(rec(casimir_on_shell:="-m^2", stiffness_verified:=true, potential_verified:=true, force_verified:=true, sample_nonnegative:=true, edges:=Length(edges)));
QUIT;
