theory NuclearPhononMetriplecticBridge
  imports Complex_Main
begin

datatype bridge_concept =
  B_Nuclear_Phonon
| B_IBM_U6_Bilinear_Generator
| B_Quadrupole_d_dagger_s
| B_Sp6R_Raising_Generator
| B_Noncompact_Dilation_Shear
| B_Casimir_Dilation_Spring
| B_Metriplectic_Evolution
| B_Wasserstein_Gradient_Flow
| B_Legendre_Fenchel_Duality

datatype bridge_edge =
  b_represented_by
| b_counted_by
| b_decomposes_into
| b_quantizes
| b_drives_irreversible_flow
| b_metric_part
| b_stabilized_by

definition bridgeEdgeHolds :: "bridge_concept => bridge_edge => bridge_concept => bool" where
  "bridgeEdgeHolds a e b =
    ((a = B_Nuclear_Phonon \<and> e = b_represented_by \<and> b = B_IBM_U6_Bilinear_Generator) \<or>
     (a = B_IBM_U6_Bilinear_Generator \<and> e = b_counted_by \<and> b = B_Quadrupole_d_dagger_s) \<or>
     (a = B_Nuclear_Phonon \<and> e = b_represented_by \<and> b = B_Sp6R_Raising_Generator) \<or>
     (a = B_Sp6R_Raising_Generator \<and> e = b_decomposes_into \<and> b = B_Noncompact_Dilation_Shear) \<or>
     (a = B_Noncompact_Dilation_Shear \<and> e = b_quantizes \<and> b = B_Casimir_Dilation_Spring) \<or>
     (a = B_Noncompact_Dilation_Shear \<and> e = b_drives_irreversible_flow \<and> b = B_Metriplectic_Evolution) \<or>
     (a = B_Metriplectic_Evolution \<and> e = b_metric_part \<and> b = B_Wasserstein_Gradient_Flow) \<or>
     (a = B_Metriplectic_Evolution \<and> e = b_stabilized_by \<and> b = B_Legendre_Fenchel_Duality))"

definition bridgePoincareC1 :: "rat => rat" where "bridgePoincareC1 m = -m*m"
definition bridgeStiffness :: "rat => rat" where "bridgeStiffness C1 = -C1"
definition bridgeUDimension :: "nat => nat" where "bridgeUDimension n = n*n"
definition bridgeSpRealDimensionFromHalfRank :: "nat => nat" where
  "bridgeSpRealDimensionFromHalfRank n = n*(2*n+1)"

theorem bridge_kernel:
  "bridgeEdgeHolds B_Noncompact_Dilation_Shear b_drives_irreversible_flow B_Metriplectic_Evolution = True \<and>
   bridgeEdgeHolds B_Metriplectic_Evolution b_metric_part B_Wasserstein_Gradient_Flow = True \<and>
   bridgeUDimension 6 = 36 \<and>
   bridgeSpRealDimensionFromHalfRank 3 = 21 \<and>
   bridgeStiffness (bridgePoincareC1 3) = 9 \<and>
   (13::nat) = 13"
  by (simp add: bridgeEdgeHolds_def bridgeUDimension_def bridgeSpRealDimensionFromHalfRank_def
      bridgePoincareC1_def bridgeStiffness_def)

end
