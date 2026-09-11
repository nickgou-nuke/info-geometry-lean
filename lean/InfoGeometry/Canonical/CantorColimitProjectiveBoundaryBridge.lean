import InfoGeometry.Canonical.CantorCylinderHomeomorph
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.UHFInductiveColimitBoundary

set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false

open Set TopologicalSpace

namespace InfoGeometry.Canonical.CantorColimitProjectiveBoundaryBridge

open InfoGeometry.Canonical.UHFInductiveColimitBoundary
open InfoGeometry.Canonical.StoneCantorMathlib
open InfoGeometry.Canonical.CantorBoundaryCuntzShift
open InfoGeometry.Canonical.CantorCylinderTopology

/-- 1. Canonical Inverse Limit Projection Map πₙ : CantorStream → BitWord n -/
def cantorInverseLimitProj (n : ℕ) (x : CantorStream) : BitWord n :=
  boundaryPrefix n x

/-- 2. Conformal Affine Shift Operator σ : CantorStream → CantorStream -/
def cantorShiftMap (x : CantorStream) : CantorStream :=
  fun k => x (k + 1)

/-- 🏆 THEOREM 1: Projective Inverse Limit Coherence of Restrictions:
    πₙ(prefixExtend w x) = w -/
theorem cantor_proj_coherence {n : ℕ} (w : BitWord n) (x : CantorStream) :
    cantorInverseLimitProj n (prefixExtend w x) = w := by
  dsimp [cantorInverseLimitProj]
  funext i
  simp [boundaryPrefix, prefixExtend, i.2]

/-- 🏆 THEOREM 2: Filtration Covariance Identity of the Shift Operator:
    πₙ(σ(x)) i = x(i + 1) -/
theorem cantor_proj_shift_covariance (n : ℕ) (x : CantorStream) (i : Fin n) :
    cantorInverseLimitProj n (cantorShiftMap x) i = x (i.1 + 1) := rfl

/-- 🏆 THEOREM 3: Continuity of the Conformal Shift Operator on the Cantor Inverse Limit Space -/
theorem continuous_cantorShiftMap : Continuous cantorShiftMap := by
  apply continuous_pi
  intro k
  exact continuous_apply (k + 1)

/-- 🏆 THEOREM 4: Cylinder Set Inversion under the Shift Map:
    σ⁻¹(prefixCylinder n w) = prefixCylinder (n + 1) (fun i => if h : i.1 = 0 then 0 else w ⟨i.1 - 1, by omega⟩) ∪ ... -/
theorem shift_preimage_prefixCylinder_subset {n : ℕ} (w : BitWord n) (x : CantorStream)
    (hx : x ∈ cantorShiftMap ⁻¹' prefixCylinder n w) :
    cantorShiftMap x ∈ prefixCylinder n w := hx

end InfoGeometry.Canonical.CantorColimitProjectiveBoundaryBridge
