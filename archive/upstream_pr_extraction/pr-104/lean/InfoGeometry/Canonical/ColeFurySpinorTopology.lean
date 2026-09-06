import Mathlib.Topology.Basic
import InfoGeometry.Algebra.SplitOctonionColeFurySpinorBridge

namespace InfoGeometry.Canonical.ColeFurySpinorTopology

open InfoGeometry.Algebra.ColeFurySpinorBridge

instance : TopologicalSpace (ColeFurySpinor ℝ) :=
  inferInstanceAs (TopologicalSpace (Fin 32 → ℝ))

/-- The finite Euclidean squared-coordinate readout on the real spinor carrier. -/
def spinorEnergy (ψ : ColeFurySpinor ℝ) : ℝ :=
  ∑ i : Fin 32, (ψ i) ^ 2

/-- The finite spinor energy is continuous in the product topology. -/
theorem continuous_spinorEnergy :
    Continuous (spinorEnergy : ColeFurySpinor ℝ → ℝ) := by
  unfold spinorEnergy
  apply continuous_finset_sum
  intro i hi
  exact (continuous_apply i).pow 2

/-- The finite spinor energy is nonnegative. -/
theorem spinorEnergy_nonneg (ψ : ColeFurySpinor ℝ) :
    0 ≤ spinorEnergy ψ := by
  unfold spinorEnergy
  exact Finset.sum_nonneg (fun i hi => sq_nonneg (ψ i))

/-- Every energy sublevel is closed in the finite spinor carrier. -/
theorem spinorEnergy_sublevel_isClosed (c : ℝ) :
    IsClosed {ψ : ColeFurySpinor ℝ | spinorEnergy ψ ≤ c} := by
  change IsClosed (spinorEnergy ⁻¹' Set.Iic c)
  exact isClosed_Iic.preimage continuous_spinorEnergy

end InfoGeometry.Canonical.ColeFurySpinorTopology
