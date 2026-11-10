import Omega.Folding.FoldBinDegeneracyTailCapacityKinks

namespace Omega.Zeta

/-- Paper label: `thm:xi-foldbin-critical-capacity-broken-line`. -/
theorem paper_xi_foldbin_critical_capacity_broken_line
    : Omega.Folding.foldBinDegeneracyCapacityLimit := by
  exact Omega.Folding.paper_fold_bin_degeneracy_tail_capacity_kinks.2

end Omega.Zeta
