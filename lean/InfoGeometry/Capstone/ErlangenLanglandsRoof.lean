import InfoGeometry.Capstone.CommutantMoebiusLegendre
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Capstone.ErlangenLanglandsConnesCapstone
import InfoGeometry.Capstone.FockCapstone

/-!
# Erlangen--Langlands Roof

This is an aggregation layer, not a proof substitute.  It re-exports the
kernel-checked theorem surfaces from the owner capstones and leaves analytic
Fredholm/zeta/Klein-bottle claims outside theorem form until there are native
Lean owners for them.
-/

namespace InfoGeometry.Capstone.ErlangenLanglandsRoof

export InfoGeometry.Capstone.ErlangenLanglandsConnesCapstone
  (ErlangenO55Statement
   erlangen_o55_invariants
   LanglandsGaloisSeparationStatement
   langlands_galois_state_separation
   ConnesAnomalyDikinStatement
   connes_anomaly_and_dikin_readout
   TomitaJMatrixStatement
   tomita_j_matrix_readout
   FibonacciQuantumGroupStatement
   fibonacci_quantum_group_readout
   TrinityCapstoneStatement
   trinity_capstone_unified)

export InfoGeometry.Capstone.CommutantMoebiusLegendre
  (finite_commutant_moebius_fenchel_mirror_o55_window
   supplied_o55_and_dirac_hodge_trace_window)

export InfoGeometry.Capstone.FockCapstone
  (same_mode_car
   cross_annihilate_anticomm
   cross_mixed_anticomm
   Jmode_comm_swap
   splitCliffordMap_refl
   splitCliffordMap_succ
   splitCliffordMap_trans
   splitCliffordMap_apply_trans
   splitCliffordInfinity_exists_of
   splitCliffordInfinity_boundary_expands
   splitCliffordInfinity_unbounded_representatives
   map_unital
   map_star
   map_real_fixed_point_of_half_branch_scaling)

end InfoGeometry.Capstone.ErlangenLanglandsRoof
