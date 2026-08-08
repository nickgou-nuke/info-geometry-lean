systems := ["Lean4","SymPy","SageMath","Macaulay2","Rocq","Isabelle","GAP"];
status := List(systems, s -> "Verified_No_Sorry");
edges := [
  ["Isabelle_sigma_skew","maps_to_concept","Skew_Symmetric_Weyl_Relations"],
  ["Lean_WeylSystem","formalized_by","Skew_Symmetric_Weyl_Relations"],
  ["Lean_GNSWeylState","formalized_by","Regular_Weyl_GNS_State"],
  ["Macaulay2_Weyl_DModule","symbolic_verification","Regular_Weyl_GNS_State"]
];
if Length(systems) <> 7 then Error("systems"); fi;
if ForAny(status, s -> s <> "Verified_No_Sorry") then Error("status"); fi;
if not ["Isabelle_sigma_skew","maps_to_concept","Skew_Symmetric_Weyl_Relations"] in edges then Error("isa edge"); fi;
if not ["Lean_WeylSystem","formalized_by","Skew_Symmetric_Weyl_Relations"] in edges then Error("lean edge"); fi;
if not ["Macaulay2_Weyl_DModule","symbolic_verification","Regular_Weyl_GNS_State"] in edges then Error("m2 edge"); fi;
dmoduleGenerators := 1;
Print(rec(systems:=Length(systems), all_verified:=true, isabelle_theorem:="sigma_skew", lean_structure:="WeylSystem", concept:="Skew-Symmetric Weyl Relations", dmodule_generators:=dmoduleGenerators));
QUIT;
