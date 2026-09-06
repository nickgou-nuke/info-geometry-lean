import InfoGeometry.Clifford.BottPeriodicity
import InfoGeometry.Canonical.RealCliffordStageDimension

open scoped TensorProduct

/-!
# Hyperbolic `Cl(1,1)` stabilization

This file gives the split-signature interpretation of the existing graded
Clifford equivalence.  It does not claim the full real Bott classification or
an abstract Morita theorem: those require separate categorical data.
-/

namespace InfoGeometry.Clifford.HyperbolicStabilization

open InfoGeometry.Clifford.BottPeriodicity
open InfoGeometry.Clifford.Cl11TensorTower
open InfoGeometry.CliffordTower

/-- Signature difference, recorded as an integer to avoid natural subtraction. -/
def signatureDifference (p q : ℕ) : ℤ := (p : ℤ) - (q : ℤ)

@[simp]
theorem signatureDifference_add_one_add_one (p q : ℕ) :
    signatureDifference (p + 1) (q + 1) = signatureDifference p q := by
  simp [signatureDifference]

/-- The repository-native one-step hyperbolic stabilization. -/
noncomputable def hyperbolicStep (n : ℕ) :
    SplitBottClifford (n + 1)
      ≃ₐ[ℝ]
        (CliffordAlgebra.evenOdd Q11 ᵍ⊗[ℝ]
          CliffordAlgebra.evenOdd (SplitBottQuad n)) :=
  splitBottStep n

@[simp]
theorem hyperbolicStep_eq_splitBottStep (n : ℕ) :
    hyperbolicStep n = splitBottStep n :=
  rfl

/-- The split step preserves the signature difference `(n,n)`. -/
theorem hyperbolicStep_signatureDifference (n : ℕ) :
    signatureDifference (n + 1) (n + 1) =
      signatureDifference n n := by
  exact signatureDifference_add_one_add_one n n

/-- The dimension recurrence of the native matrix tower under stabilization. -/
theorem hyperbolicStep_stage_finrank (n : ℕ) :
    Module.finrank ℝ (MatStage (n + 1)) =
      4 * Module.finrank ℝ (MatStage n) := by
  rw [InfoGeometry.Canonical.RealCliffordStageDimension.matStage_finrank_succ]

end InfoGeometry.Clifford.HyperbolicStabilization
