EntropyProduction := function(S0,S1) return AbsInt(S1-S0); end;
for S0 in [-5..5] do
  for S1 in [-5..5] do
    if EntropyProduction(S0,S1) < 0 then Error("entropy"); fi;
  od;
od;
edges := [
  ["Souriau_Lie_Group_Thermodynamics","has_leaflet","Entropic_Leaflet"],
  ["Entropic_Leaflet","tangent_reversible_flow","Sars_Weyl_Colimit"],
  ["Sars_Weyl_Colimit","parameterizes_scale_orthogonal_to_leaves","Souriau_Lie_Group_Thermodynamics"],
  ["Partition_Function_Normalization","normalizes_by_partition_function","Dilaton_Weyl_Gauge_Vector"],
  ["Dilaton_Weyl_Gauge_Vector","generates_orthogonal_entropy_transport","Orthogonal_Entropy_Transport"]
];
if Length(edges) <> 5 then Error("edges"); fi;
Print(rec(entropy_production_sample_nonnegative:=true, graphEdges:=Length(edges), partition_rescale:="Z*rho=w", dilaton_square_weyl_scale:="phi^2=scale"));
QUIT;
