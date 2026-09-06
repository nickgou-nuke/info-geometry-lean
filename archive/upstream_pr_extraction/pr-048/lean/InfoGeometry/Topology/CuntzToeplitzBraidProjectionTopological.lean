import Mathlib
import InfoGeometry.Physics.Algebra.CuntzToeplitzBraidRepresentation

/-!
# Topological Cuntz--Toeplitz braid projection readout

This file packages the already-proved continuous parameter dependence of the
Cuntz braid projection operator as a topological owner.  It does not claim a
new C*-dynamics or automorphism flow.
-/

namespace InfoGeometry.Topology.CuntzToeplitzBraidProjectionTopological

open InfoGeometry.Physics.Algebra

noncomputable section

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The Cuntz braid projection operator as a continuous parameterized map. -/
def braidProjectionMap (O2 : CuntzTwoAlgebra A) : ℝ × ℝ → A :=
  fun p => cuntzBraidProjectionOperator O2 p.1 p.2

theorem continuous_braidProjectionMap
    (O2 : CuntzTwoAlgebra A) :
    Continuous (braidProjectionMap O2) := by
  simpa [braidProjectionMap] using
    (continuous_cuntzBraidProjectionOperator (A := A) O2)

/-- The braid projection remains continuous on the diagonal parameter slice. -/
theorem continuous_braidProjectionMap_diag
    (O2 : CuntzTwoAlgebra A) :
    Continuous (fun t : ℝ => braidProjectionMap O2 (t, t)) := by
  exact (continuous_braidProjectionMap (A := A) O2).comp
    (continuous_id.prodMk continuous_id)

@[simp] theorem braidProjectionMap_apply
    (O2 : CuntzTwoAlgebra A) (q₁ q₂ : ℝ) :
    braidProjectionMap O2 (q₁, q₂) =
      cuntzBraidProjectionOperator O2 q₁ q₂ := rfl

end
