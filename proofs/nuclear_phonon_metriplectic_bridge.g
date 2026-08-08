Concepts := [
  "Nuclear_Phonon",
  "IBM_U6_Bilinear_Generator",
  "Quadrupole_d_dagger_s",
  "Sp6R_Raising_Generator",
  "Noncompact_Dilation_Shear",
  "Casimir_Dilation_Spring",
  "Metriplectic_Evolution",
  "Wasserstein_Gradient_Flow",
  "Legendre_Fenchel_Duality"
];;

Edges := [
  ["Nuclear_Phonon","represented_by","IBM_U6_Bilinear_Generator"],
  ["IBM_U6_Bilinear_Generator","counted_by","Quadrupole_d_dagger_s"],
  ["Nuclear_Phonon","represented_by","Sp6R_Raising_Generator"],
  ["Sp6R_Raising_Generator","decomposes_into","Noncompact_Dilation_Shear"],
  ["Noncompact_Dilation_Shear","quantizes","Casimir_Dilation_Spring"],
  ["Noncompact_Dilation_Shear","drives_irreversible_flow","Metriplectic_Evolution"],
  ["Metriplectic_Evolution","metric_part","Wasserstein_Gradient_Flow"],
  ["Metriplectic_Evolution","stabilized_by","Legendre_Fenchel_Duality"]
];;

if Length(Concepts) <> 9 then Error("concept count"); fi;
if Length(Edges) <> 8 then Error("edge count"); fi;
if not ["Noncompact_Dilation_Shear","drives_irreversible_flow","Metriplectic_Evolution"] in Edges then Error("bridge edge"); fi;
if 6*6 <> 36 then Error("u6"); fi;
if 3*(2*3+1) <> 21 then Error("sp6"); fi;
if -(-3*3) <> 9 then Error("spring"); fi;

Print(rec(concepts:=Length(Concepts), edges:=Length(Edges), milestone13:=13,
  u6Dim:=36, sp6RDim:=21, springK_m3:=9), "\n");
QUIT;
