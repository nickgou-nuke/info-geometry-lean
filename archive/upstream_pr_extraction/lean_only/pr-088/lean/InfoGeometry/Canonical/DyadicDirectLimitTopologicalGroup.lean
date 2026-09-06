import InfoGeometry.Canonical.DyadicDirectLimitTopologicalAdditive
import Mathlib.Topology.Algebra.Group.Basic

namespace InfoGeometry.Canonical

/-!
# Topological additive-group structure of the dyadic direct-limit carrier

The transported topology and the concrete additive-group operations satisfy
Mathlib's `IsTopologicalAddGroup` interface.  Consequently the standard
continuity theorems for integer scalar multiplication apply.
-/

noncomputable instance dyadicDirectLimitIsTopologicalAddGroup :
    IsTopologicalAddGroup DyadicDirectLimit where
  continuous_add := continuous_dyadicDirectLimit_add
  continuous_neg := continuous_dyadicDirectLimit_neg

theorem continuous_dyadicDirectLimit_zsmul (z : ℤ) :
    Continuous (fun x : DyadicDirectLimit => z • x) := by
  exact (continuous_zsmul :
    ∀ z : ℤ, Continuous (fun x : DyadicDirectLimit => z • x)) z

theorem continuous_dyadicDirectLimit_int_smul :
    Continuous
      (fun p : ℤ × DyadicDirectLimit => p.1 • p.2) := by
  exact continuous_prod_of_discrete_left.mpr (continuous_zsmul :
    ∀ z : ℤ, Continuous (fun x : DyadicDirectLimit => z • x))

end InfoGeometry.Canonical
