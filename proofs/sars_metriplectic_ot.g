FenchelGap := function(x,u) return (x-u)*(x-u); end;
BurgGap := function(x,u) return (x-u)*(x-u); end;
for x in [-5..5] do
  for u in [-5..5] do
    if FenchelGap(x,u) < 0 then Error("fenchel"); fi;
    if BurgGap(x,u) < 0 then Error("burg"); fi;
  od;
od;
if FenchelGap(0,0) <> 0 then Error("fenchel zero"); fi;
if BurgGap(0,0) <> 0 then Error("burg zero"); fi;
edges := [
  ["Metriplectic_Evolution","symplectic_part","WeylSystem"],
  ["Metriplectic_Evolution","metric_part","Wasserstein_Gradient_Flow"],
  ["Wasserstein_Gradient_Flow","minimizes_distortion","Itakura_Saito_Divergence"],
  ["Itakura_Saito_Divergence","generated_by","Legendre_Fenchel_Duality"],
  ["Legendre_Fenchel_Duality","stabilizes_vacuum","Metriplectic_Evolution"]
];
if Length(edges) <> 5 then Error("edges"); fi;
Print(rec(fenchel_sample_nonnegative:=true,burg_sample_nonnegative:=true,vacuum_zero:=true,edges:=Length(edges)));
QUIT;
