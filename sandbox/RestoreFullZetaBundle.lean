import InfoGeometry.Clifford.LogCftMonodromy
import InfoGeometry.Arithmetic.PrimitiveSetsAbove
import InfoGeometry.Canonical.BostConnesKMS

/-!
# RestoreFullZetaBundle

Small sandbox bundle combining monodromy, primitive-weight, and KMS readbacks.
-/

namespace InfoGeometry.Restore.FullZetaBundle

open Matrix
open InfoGeometry.Clifford.LogCftMonodromy

/-- A tiny combined packet of restored facts. -/
theorem restore_full_zeta_bundle (h : ℂ) (n : ℕ) (β ζβ : ℝ) (m : ℕ+) :
    (hadjiivanovMonodromy h).det = lcftPhase h ^ 2 ∧
    0 ≤ InfoGeometry.Arithmetic.primitiveWeight n ∧
    InfoGeometry.Canonical.BostConnesKMS.kmsProjectionWeight β ζβ m =
      ((m : ℕ) : ℝ) ^ (-β) / ζβ := by
  refine ⟨?_, ?_, ?_⟩
  · exact monodromy_is_parabolic h
  · exact InfoGeometry.Arithmetic.primitiveWeight_nonneg n
  · exact InfoGeometry.Canonical.BostConnesKMS.kmsProjectionWeight_eq β ζβ m

end InfoGeometry.Restore.FullZetaBundle
