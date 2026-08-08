theory SarsSouriauDilaton
  imports Main
begin

datatype concept = Souriau_Lie_Group_Thermodynamics | Sars_Weyl_Colimit | Entropic_Leaflet | Dilaton_Weyl_Gauge_Vector | Partition_Function_Normalization | Orthogonal_Entropy_Transport
datatype edge = has_leaflet | tangent_reversible_flow | parameterizes_scale_orthogonal_to_leaves | normalizes_by_partition_function | generates_orthogonal_entropy_transport

fun edgeHolds :: "concept => edge => concept => bool" where
  "edgeHolds Souriau_Lie_Group_Thermodynamics has_leaflet Entropic_Leaflet = True" |
  "edgeHolds Entropic_Leaflet tangent_reversible_flow Sars_Weyl_Colimit = True" |
  "edgeHolds Sars_Weyl_Colimit parameterizes_scale_orthogonal_to_leaves Souriau_Lie_Group_Thermodynamics = True" |
  "edgeHolds Partition_Function_Normalization normalizes_by_partition_function Dilaton_Weyl_Gauge_Vector = True" |
  "edgeHolds Dilaton_Weyl_Gauge_Vector generates_orthogonal_entropy_transport Orthogonal_Entropy_Transport = True" |
  "edgeHolds _ _ _ = False"

definition partition_rescale :: "int => int => int => bool" where "partition_rescale Z rho w = (Z*rho = w)"
definition dilaton_square_weyl_scale :: "int => int => bool" where "dilaton_square_weyl_scale phi scale = (phi*phi = scale)"
definition entropy_production :: "int => int => int" where "entropy_production S0 S1 = abs (S1-S0)"

theorem entropy_production_nonneg: "0 <= entropy_production S0 S1"
  by (simp add: entropy_production_def)

theorem souriau_dilaton_kernel:
  "(\<forall>S0 S1. 0 <= entropy_production S0 S1) \<and>
   edgeHolds Souriau_Lie_Group_Thermodynamics has_leaflet Entropic_Leaflet = True \<and>
   edgeHolds Entropic_Leaflet tangent_reversible_flow Sars_Weyl_Colimit = True \<and>
   edgeHolds Sars_Weyl_Colimit parameterizes_scale_orthogonal_to_leaves Souriau_Lie_Group_Thermodynamics = True \<and>
   edgeHolds Partition_Function_Normalization normalizes_by_partition_function Dilaton_Weyl_Gauge_Vector = True \<and>
   edgeHolds Dilaton_Weyl_Gauge_Vector generates_orthogonal_entropy_transport Orthogonal_Entropy_Transport = True"
  by (simp add: entropy_production_nonneg)

end
