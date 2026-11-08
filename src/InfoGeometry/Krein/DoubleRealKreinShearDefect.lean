import InfoGeometry.Krein.DoubledSpaceRealKANBridge

/-!
# Pairing defect of the canonical doubled-space parabolic shear

The real KAN shear acts on `DoubledSpace E` by `(x, ξ) ↦ (x + t • ξ, ξ)`.
This file computes its exact defect against the canonical diagonal Krein
pairing. The action is generally not Krein-isometric.
-/

noncomputable section

namespace InfoGeometry.Krein.DoubleRealKreinShearDefect

open scoped InnerProductSpace
open InfoGeometry.Krein
open InfoGeometry.Krein.DoubledSpaceMatrixClockBridge
open InfoGeometry.Krein.DoubledSpaceRealKANBridge

variable {E : Type*}
variable [NormedAddCommGroup E]
variable [InnerProductSpace ℝ E]
variable [CompleteSpace E]

/-- Exact change in the canonical Krein pairing under the upper parabolic
    shear on the doubled real carrier. -/
theorem kreinInner_componentNReal_defect (t : ℝ) (x ξ y η : E) :
    KreinSpace.kreinInner
        (ρclock (E := E) (componentNReal t) (to_doubled x ξ))
        (ρclock (E := E) (componentNReal t) (to_doubled y η)) -
      KreinSpace.kreinInner (to_doubled x ξ) (to_doubled y η) =
        t * (inner ℝ x η + inner ℝ ξ y) + t ^ 2 * inner ℝ ξ η := by
  rw [ρclock_componentNReal_apply, ρclock_componentNReal_apply,
    krein_inner_prod_l2, krein_inner_prod_l2]
  simp only [WithLp.ofLp_toLp]
  simp [inner_add_left, inner_add_right, real_inner_smul_left,
    real_inner_smul_right, smul_eq_mul]
  ring

/-- A nonzero shear changes the Krein quadratic value on a pure second-sheet
    vector by `t² * inner ℝ ξ ξ`. -/
theorem kreinInner_componentNReal_secondSheet_defect
    (t : ℝ) (ξ : E) :
    KreinSpace.kreinInner
        (ρclock (E := E) (componentNReal t) (to_doubled 0 ξ))
        (ρclock (E := E) (componentNReal t) (to_doubled 0 ξ)) -
      KreinSpace.kreinInner (to_doubled 0 ξ) (to_doubled 0 ξ) =
        t ^ 2 * inner ℝ ξ ξ := by
  have h := kreinInner_componentNReal_defect (E := E) t 0 ξ 0 ξ
  simpa using h

/-- On a nonzero doubled carrier, every nonzero upper shear fails to be a
    Krein isometry for the canonical diagonal form. -/
theorem componentNReal_not_krein_isometry
    (t : ℝ) (ht : t ≠ 0) (ξ : E) (hξ : ξ ≠ 0) :
    ¬ KreinSpace.IsKreinIsometry
        (ρclock (E := E) (componentNReal t)) := by
  intro hIso
  have hpair := hIso (to_doubled 0 ξ) (to_doubled 0 ξ)
  have hdefect := kreinInner_componentNReal_secondSheet_defect (E := E) t ξ
  rw [hpair] at hdefect
  have ht2 : 0 < t ^ 2 := sq_pos_of_ne_zero ht
  have hξ2 : 0 < inner ℝ ξ ξ := real_inner_self_pos.mpr hξ
  have hprod : 0 < t ^ 2 * inner ℝ ξ ξ := mul_pos ht2 hξ2
  linarith

end InfoGeometry.Krein.DoubleRealKreinShearDefect
