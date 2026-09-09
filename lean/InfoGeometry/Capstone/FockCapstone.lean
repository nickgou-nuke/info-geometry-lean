import InfoGeometry.Canonical.SplitCliffordFiniteCAR
import InfoGeometry.Canonical.SplitCliffordTensorBridge
import InfoGeometry.Canonical.SplitCliffordDirectLimit
import InfoGeometry.Topology.CuntzMap
import InfoGeometry.Capstone.ErlangenLanglandsConnesCapstone

/-!
# Fock Capstone -- Owner-Backed Readouts

This file keeps only kernel-checked Fock/CAR/tower/Cuntz/O55 readouts.
The Stone--von Neumann identification with the infinite CAR representation,
the global `O(∞,∞)` action, and the zeta function of the Cantor spectral
triple are not proved here.
-/

namespace InfoGeometry.Capstone.FockCapstone

open InfoGeometry.Canonical.SplitCliffordFiniteCAR

export InfoGeometry.Canonical.SplitCliffordFiniteCAR
  (same_mode_car
   cross_annihilate_anticomm
   cross_mixed_anticomm
   Jmode_comm_swap)

export InfoGeometry.Canonical.SplitCliffordTensorBridge
  (SplitCl55Carrier
   SplitCl55Quad
   SplitCl55Alg
   splitCl55_headCl11TensorCl44Equiv
   SplitCl55TailHeadTensorStep
   splitCl55_cl44TensorCl11Equiv
   splitCl55_headCl11TensorCl44Equiv_eq_owner
   splitCl55_headFactor
   splitCl55_tailFactor)

export InfoGeometry.Canonical.SplitCliffordDirectLimit
  (splitCliffordMap_refl
   splitCliffordMap_succ
   splitCliffordMap_trans
   splitCliffordMap_apply_trans
   splitCliffordDirectedSystem
   splitCliffordInfinity_exists_of
   splitCliffordInfinity_boundary_expands
   splitCliffordInfinity_unbounded_representatives
   splitCliffordInfinity_cl55_window_absorbs_finite_tail
   splitCliffordInfinity_has_representative_beyond_cl55_window)

export InfoGeometry.Topology.CuntzMap
  (map_unital
   map_star
   map_real_fixed_point_of_half_branch_scaling
   discrete_modular_flow_apply_eq_map
   discrete_modular_flow_real_fixed_point_of_half_branch_scaling)

export InfoGeometry.Capstone.ErlangenLanglandsConnesCapstone
  (erlangen_o55_invariants)

/- [1] FINITE CAR --------------------------------------------------------- -/

end InfoGeometry.Capstone.FockCapstone
