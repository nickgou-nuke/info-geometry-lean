import InfoGeometry.Clifford.LogCftMonodromy
import InfoGeometry.Canonical.BostConnesKMS

/-!
# RestoreMonodromyKMSPacket2

Small sandbox packet for monodromy and KMS projection readbacks.
-/

namespace InfoGeometry.Restore.MonodromyKMSPacket2

open Matrix
open InfoGeometry.Clifford.LogCftMonodromy
open scoped BigOperators

variable {Op : Type*} [Ring Op] [StarRing Op]

/-- The monodromy determinant is the repeated phase square. -/
theorem monodromy_is_parabolic_restore (h : ℂ) :
    (hadjiivanovMonodromy h).det = lcftPhase h ^ 2 := by
  exact monodromy_is_parabolic h

/-- The `n`-fold monodromy follows the winding law. -/
theorem hadjiivanovMonodromy_pow_winding_restore (h : ℂ) (n : ℕ) :
    hadjiivanovMonodromy h ^ n =
      lcftPhase h ^ n •
        ((1 : Matrix (Fin 2) (Fin 2) ℂ) +
          ((n : ℂ) * logShearBase) • jordanNilpotent) := by
  exact hadjiivanovMonodromy_pow_winding h n

/-- Normalized KMS Boltzmann weight. -/
theorem kmsProjectionWeight_eq_restore (β ζβ : ℝ) (n : ℕ+) :
    InfoGeometry.Canonical.BostConnesKMS.kmsProjectionWeight β ζβ n =
      ((n : ℕ) : ℝ) ^ (-β) / ζβ := by
  exact InfoGeometry.Canonical.BostConnesKMS.kmsProjectionWeight_eq β ζβ n

/-- KMS evaluation on projections. -/
theorem kms_evaluation_on_projections_restore
    (C : InfoGeometry.Canonical.BostConnesKMS.BostConnesCuntzSystem Op)
    (Φ : InfoGeometry.Canonical.BostConnesKMS.KMSProjectionState C)
    (n m : ℕ+) :
    Φ.φ (star (InfoGeometry.Canonical.BostConnesKMS.S C n) * InfoGeometry.Canonical.BostConnesKMS.S C m) =
      if n = m then ((n : ℕ) : ℝ) ^ (-Φ.β) / Φ.ζβ else 0 := by
  exact InfoGeometry.Canonical.BostConnesKMS.KMSProjectionState.kms_evaluation_on_projections Φ n m

end InfoGeometry.Restore.MonodromyKMSPacket2
