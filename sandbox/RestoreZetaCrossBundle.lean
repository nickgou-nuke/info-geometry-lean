import InfoGeometry.Arithmetic.PrimitiveSetsAbove
import InfoGeometry.Clifford.LogCftMonodromy
import InfoGeometry.Canonical.BostConnesKMS

/-!
# RestoreZetaCrossBundle

Tiny cross-bridge sandbox theorem bundling monodromy, primitive-weight, and KMS readbacks.
-/

namespace InfoGeometry.Restore.ZetaCrossBundle

open Matrix
open InfoGeometry.Clifford.LogCftMonodromy

/-- A compact bundle of restored zeta-adjacent facts. -/
theorem restore_zeta_cross_bundle (h : ℂ) (A : Finset ℕ) (β ζβ : ℝ) (n : ℕ+) :
    (hadjiivanovMonodromy h).det = lcftPhase h ^ 2 ∧
    0 ≤ InfoGeometry.Arithmetic.primitiveWeightSum A ∧
    InfoGeometry.Canonical.BostConnesKMS.kmsProjectionWeight β ζβ n =
      ((n : ℕ) : ℝ) ^ (-β) / ζβ := by
  refine ⟨?_, ?_, ?_⟩
  · exact monodromy_is_parabolic h
  · exact InfoGeometry.Arithmetic.primitiveWeightSum_nonneg A
  · exact InfoGeometry.Canonical.BostConnesKMS.kmsProjectionWeight_eq β ζβ n

end InfoGeometry.Restore.ZetaCrossBundle
