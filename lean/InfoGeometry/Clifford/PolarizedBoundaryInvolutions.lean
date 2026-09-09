import InfoGeometry.Clifford.PolarizedMinkowski55

/-! Intrinsic involutions of the polarized boundary carrier.  Topological and
Clifford interpretations are downstream of this finite layer. -/

namespace InfoGeometry.Clifford.PolarizedBoundaryInvolutions

open InfoGeometry.Clifford.PolarizedMinkowski55

abbrev Boundary55 := PolarizedMinkowski55.Boundary55

def mixedSwap : Boundary55 ≃ₗ[ℝ] Boundary55 :=
  vectorFlip.trans pairSwap

@[simp] theorem pairSwap_sq (z : Boundary55) : pairSwap (pairSwap z) = z := rfl

@[simp] theorem vectorFlip_sq (z : Boundary55) : vectorFlip (vectorFlip z) = z := by
  simp [vectorFlip]

theorem swap_flip_commute (z : Boundary55) :
    pairSwap (vectorFlip z) = vectorFlip (pairSwap z) := rfl

@[simp] theorem mixedSwap_sq (z : Boundary55) : mixedSwap (mixedSwap z) = z := by
  change pairSwap (vectorFlip (pairSwap (vectorFlip z))) = z
  rw [show vectorFlip (pairSwap (vectorFlip z)) =
      pairSwap (vectorFlip (vectorFlip z)) by rfl]
  simp

theorem pairSwap_preserves (z : Boundary55) :
    boundaryQuadratic (pairSwap z) = boundaryQuadratic z := by
  exact PolarizedMinkowski55.pairSwap_preserves z

theorem vectorFlip_preserves (z : Boundary55) :
    boundaryQuadratic (vectorFlip z) = boundaryQuadratic z := by
  exact PolarizedMinkowski55.vectorFlip_preserves z

theorem mixedSwap_preserves (z : Boundary55) :
    boundaryQuadratic (mixedSwap z) = boundaryQuadratic z := by
  change boundaryQuadratic (pairSwap (vectorFlip z)) = _
  rw [pairSwap_preserves, vectorFlip_preserves]

def fundamentalSymmetry : Boundary55 ≃ₗ[ℝ] Boundary55 := pairSwap

@[simp] theorem fundamentalSymmetry_sq (z : Boundary55) :
    fundamentalSymmetry (fundamentalSymmetry z) = z := by
  simp [fundamentalSymmetry]

theorem fundamentalSymmetry_preserves (z : Boundary55) :
    boundaryQuadratic (fundamentalSymmetry z) = boundaryQuadratic z := by
  exact pairSwap_preserves z

theorem mixedSwap_fixed_point : ∃ z : Boundary55, mixedSwap z = z :=
  ⟨0, by simp [mixedSwap]⟩

end InfoGeometry.Clifford.PolarizedBoundaryInvolutions
