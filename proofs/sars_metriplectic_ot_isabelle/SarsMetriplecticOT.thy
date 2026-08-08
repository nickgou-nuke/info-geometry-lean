theory SarsMetriplecticOT
  imports Main
begin

datatype concept = Metriplectic_Evolution | WeylSystem | Wasserstein_Gradient_Flow | Itakura_Saito_Divergence | Legendre_Fenchel_Duality
datatype edge = symplectic_part | metric_part | minimizes_distortion | generated_by | stabilizes_vacuum

fun edgeHolds :: "concept => edge => concept => bool" where
  "edgeHolds Metriplectic_Evolution symplectic_part WeylSystem = True" |
  "edgeHolds Metriplectic_Evolution metric_part Wasserstein_Gradient_Flow = True" |
  "edgeHolds Wasserstein_Gradient_Flow minimizes_distortion Itakura_Saito_Divergence = True" |
  "edgeHolds Itakura_Saito_Divergence generated_by Legendre_Fenchel_Duality = True" |
  "edgeHolds Legendre_Fenchel_Duality stabilizes_vacuum Metriplectic_Evolution = True" |
  "edgeHolds _ _ _ = False"

definition fenchel_quadratic_gap :: "int => int => int" where "fenchel_quadratic_gap x u = (x-u)*(x-u)"
definition burg_quadratic_gap :: "int => int => int" where "burg_quadratic_gap x u = (x-u)*(x-u)"

theorem fenchel_quadratic_nonneg: "0 <= fenchel_quadratic_gap x u"
  by (simp add: fenchel_quadratic_gap_def)

theorem burg_quadratic_nonneg: "0 <= burg_quadratic_gap x u"
  by (simp add: burg_quadratic_gap_def)

theorem metriplectic_ot_kernel:
  "(\<forall>x u. 0 <= fenchel_quadratic_gap x u) \<and>
   (\<forall>x u. 0 <= burg_quadratic_gap x u) \<and>
   fenchel_quadratic_gap 0 0 = 0 \<and>
   burg_quadratic_gap 0 0 = 0 \<and>
   edgeHolds Metriplectic_Evolution symplectic_part WeylSystem = True \<and>
   edgeHolds Metriplectic_Evolution metric_part Wasserstein_Gradient_Flow = True \<and>
   edgeHolds Wasserstein_Gradient_Flow minimizes_distortion Itakura_Saito_Divergence = True \<and>
   edgeHolds Itakura_Saito_Divergence generated_by Legendre_Fenchel_Duality = True"
  by (simp add: fenchel_quadratic_nonneg burg_quadratic_nonneg fenchel_quadratic_gap_def burg_quadratic_gap_def)

end
