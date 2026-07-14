import InfoGeometry.Projective.SplitOctonions.BoundaryPacket
import Mathlib.Tactic

/-!
# Three-dimensional split-octonion realization

This file specializes the existing projective Zorn realization to the concrete
three-vector sector.  It does not introduce a new algebra, quotient, or
projective boundary.

The point is simply:

* choose the 3D dot form on `Fin 3 → ℚ`;
* use the existing upper/lower lightray representatives;
* read back the projective incidence condition as orthogonality.

That gives the concrete 3D realization map on the Zorn null shell.
-/

namespace ThreeDimensionalRealization

open InfoGeometry.Projective.SplitOctonions
open ZornProjectiveDatum
open ZornProjectiveDatum.PolarDatum

/-- The `ℚ`-valued 3D dot product as a bilinear form. -/
noncomputable def dot3Bilin : LinearMap.BilinForm ℚ (Fin 3 → ℚ) :=
  LinearMap.mk₂ ℚ
    (fun u v =>
      (1 / 2 : ℚ) * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2))
    (by
      intro u₁ u₂ v
      simp [Pi.add_apply, Pi.smul_apply]
      ring_nf)
    (by
      intro c u v
      simp [Pi.add_apply, Pi.smul_apply]
      ring_nf)
    (by
      intro u v₁ v₂
      simp [Pi.add_apply, Pi.smul_apply]
      ring_nf)
    (by
      intro c u v
      simp [Pi.add_apply, Pi.smul_apply]
      ring_nf)

/-- The `dot3Bilin` form is symmetric. -/
theorem dot3Bilin_symm (u v : Fin 3 → ℚ) :
    dot3Bilin u v = dot3Bilin v u := by
  simp [dot3Bilin, mul_comm, add_comm, add_left_comm, add_assoc]

/-- The 3D dot form on coordinates is the standard orthogonality test. -/
theorem dot3Bilin_eq_zero_iff (u v : Fin 3 → ℚ) :
    dot3Bilin u v = 0 ↔
      u 0 * v 0 + u 1 * v 1 + u 2 * v 2 = 0 := by
  constructor
  · intro h
    have h' := congrArg (fun t : ℚ => (2 : ℚ) * t) h
    simp [dot3Bilin] at h'
    linarith
  · intro h
    simp [dot3Bilin, h]

/--
The canonical upper and lower lightray realizations are orthogonal exactly
when the 3-vector dot product vanishes.

This is the concrete 3D split-octonion realization surface.
-/
theorem upperLowerLightray_realization_iff_dot_zero
    (v w : Fin 3 → ℚ) (hv : v ≠ 0) (hw : w ≠ 0) :
    projective_polar_incidence (R := ℚ) (V := Fin 3 → ℚ) dot3Bilin
      (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum dot3Bilin)
        (upperLightrayRep (R := ℚ) (V := Fin 3 → ℚ) dot3Bilin hv))
      (ZornProjectiveDatum.nullRayMk (concreteZornProjectiveDatum dot3Bilin)
        (lowerLightrayRep (R := ℚ) (V := Fin 3 → ℚ) dot3Bilin hw))
      ↔
    v 0 * w 0 + v 1 * w 1 + v 2 * w 2 = 0 := by
  rw [projective_polar_incidence_iff (B := dot3Bilin)]
  simp [dot3Bilin, polarExpr_closed, upperLightrayRep, lowerLightrayRep]

end ThreeDimensionalRealization
