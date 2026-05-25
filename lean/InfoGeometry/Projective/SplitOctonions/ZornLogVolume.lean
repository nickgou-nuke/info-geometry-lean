import InfoGeometry.Projective.SplitOctonions.ZornInstance
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Projective.SplitOctonions.ZornLogVolume

Zorn determinant as logarithmic relative-volume potential.

This file proves the concrete log-volume consequences of the existing
Zorn determinant scaling theorem

  detZ (u • X) = u^2 detZ X.

It adds no new projective datum and no new wrapper structure.
-/

namespace InfoGeometry.Projective.SplitOctonions

noncomputable section

namespace ZornCell

variable {V : Type*}
variable [AddCommGroup V] [Module ℝ V]

/-- Negative logarithmic Zorn determinant potential. -/
def zornLogBarrier
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X : ZornCell ℝ V) : ℝ :=
  - Real.log (ZornCell.detZ B X)

/--
Radon–Nikodym-style relative Zorn volume factor:

  RN(X,Y) = detZ(Y) / detZ(X).
-/
def zornRelativeVolumeRN
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X Y : ZornCell ℝ V) : ℝ :=
  ZornCell.detZ B Y / ZornCell.detZ B X

/--
Unit coefficient is nonzero after coercion to `ℝ`.
-/
private lemma unit_coe_ne_zero (u : ℝˣ) :
    (u : ℝ) ≠ 0 := by
  exact Units.ne_zero u

/--
The determinant remains positive under unit scaling if it was positive.

This is the concrete domain-preservation statement for the positive
log-volume chart.
-/
theorem detZ_scalarScale_pos
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u : ℝˣ) (X : ZornCell ℝ V)
    (hX : 0 < ZornCell.detZ B X) :
    0 < ZornCell.detZ B (ZornCell.scalarScale u X) := by
  rw [ZornCell.detZ_scalarScale]
  exact mul_pos (sq_pos_of_ne_zero (unit_coe_ne_zero u)) hX

/--
Log-barrier scaling under componentwise Zorn unit scaling.

Because

  detZ(u • X) = u² detZ(X),

we get

  -log detZ(u • X) = -log detZ(X) - log(u²)

on the positive determinant stratum.
-/
theorem zornLogBarrier_scalarScale
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u : ℝˣ) (X : ZornCell ℝ V)
    (hX : 0 < ZornCell.detZ B X) :
    zornLogBarrier B (ZornCell.scalarScale u X)
      =
    zornLogBarrier B X - Real.log ((u : ℝ) ^ 2) := by
  unfold zornLogBarrier
  rw [ZornCell.detZ_scalarScale]
  rw [Real.log_mul
      (pow_ne_zero 2 (unit_coe_ne_zero u))
      (ne_of_gt hX)]
  ring

/--
Relative volume of a point with itself is `1` on the non-isotropic stratum.
-/
theorem zornRelativeVolumeRN_self
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0) :
    zornRelativeVolumeRN B X X = 1 := by
  unfold zornRelativeVolumeRN
  field_simp [hX]

/--
The negative logarithm of the Zorn RN relative-volume factor is the
difference of log-barrier potentials:

  -log(detZ(Y)/detZ(X)) = φ(Y) - φ(X),

where `φ(X) = -log detZ(X)`.
-/
theorem negLog_zornRelativeVolumeRN_eq_zornLogBarrier_sub
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X Y : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0)
    (hY : ZornCell.detZ B Y ≠ 0) :
    - Real.log (zornRelativeVolumeRN B X Y)
      =
    zornLogBarrier B Y - zornLogBarrier B X := by
  unfold zornRelativeVolumeRN zornLogBarrier
  rw [Real.log_div hY hX]
  ring

/--
Right scaling of the target multiplies the relative-volume factor by `u²`.
-/
theorem zornRelativeVolumeRN_scalarScale_right
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u : ℝˣ) (X Y : ZornCell ℝ V) :
    zornRelativeVolumeRN B X (ZornCell.scalarScale u Y)
      =
    ((u : ℝ) ^ 2) * zornRelativeVolumeRN B X Y := by
  unfold zornRelativeVolumeRN
  rw [ZornCell.detZ_scalarScale]
  ring

/--
Left scaling of the base divides the relative-volume factor by `u²`.
-/
theorem zornRelativeVolumeRN_scalarScale_left
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u : ℝˣ) (X Y : ZornCell ℝ V) :
    zornRelativeVolumeRN B (ZornCell.scalarScale u X) Y
      =
    (((u : ℝ) ^ 2)⁻¹) * zornRelativeVolumeRN B X Y := by
  unfold zornRelativeVolumeRN
  rw [ZornCell.detZ_scalarScale]
  field_simp [pow_ne_zero 2 (unit_coe_ne_zero u)]
  ring

/--
If the determinant scales by `u²`, then the corresponding 8-dimensional
volume Jacobian scales by `(u²)^4`.

This is only the algebraic exponent calculation.
-/
def zornVolumeJacobianOfScale (u : ℝˣ) : ℝ :=
  ((u : ℝ) ^ 2) ^ 4

/--
The 8-dimensional Jacobian exponent simplifies to `u^8`.
-/
theorem zornVolumeJacobianOfScale_eq_pow_eight
    (u : ℝˣ) :
    zornVolumeJacobianOfScale u = (u : ℝ) ^ 8 := by
  unfold zornVolumeJacobianOfScale
  ring

/--
Negative logarithm of the 8-dimensional Jacobian is the logarithmic volume
change of the determinant scale.

This keeps the statement at the scalar algebraic level; no self-concordance
or extended-real barrier is claimed here.
-/
theorem negLog_zornVolumeJacobianOfScale
    (u : ℝˣ) :
    - Real.log (zornVolumeJacobianOfScale u)
      =
    - Real.log ((u : ℝ) ^ 8) := by
  rw [zornVolumeJacobianOfScale_eq_pow_eight]

end ZornCell

end

end InfoGeometry.Projective.SplitOctonions
