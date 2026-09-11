import InfoGeometry.Projective.SplitOctonions.ZornInstance
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# InfoGeometry.Projective.SplitOctonions.ZornLogVolume

Concrete log-volume consequences of the Zorn determinant scaling law.

Existing owner theorem from `ZornInstance`:

  detZ (u • X) = u^2 * detZ X.

This file proves:

* positive determinant is preserved by unit scaling;
* the negative log determinant shifts by `- log(u^2)`;
* the relative-volume/Radon--Nikodym ratio is `detZ Y / detZ X`;
* `-log RN(X,Y) = φ(Y) - φ(X)`, where `φ = -log detZ`;
* finite-stage normalized log determinants are stable under square bonding;
* the induced dimension-8 Jacobian exponent is `u^8`.

No new projective datum.
No self-concordance claim.
No extended-real barrier claim.
-/

namespace InfoGeometry.Projective.SplitOctonions

noncomputable section

/--
Finite-stage normalized log-determinant stabilization.

This is the algebraic core behind the determinant stabilization in the
tensor-doubling tower. If the next-stage determinant is the square of the
current-stage determinant, then the volume-normalized log determinant is
unchanged:

`log(det_{N+1}) / 2^(N+1) = log(det_N) / 2^N`.

This is the finite theorem behind the trace-log / Fuglede-Kadison intuition.
It does not assert the existence of an infinite von Neumann algebra limit.
-/
theorem normalized_logdet_stable_of_square
    (δ δnext : ℝ) (N : ℕ)
    (hδ : 0 < δ)
    (hnext : δnext = δ ^ 2) :
    Real.log δnext / ((2 : ℝ) ^ (N + 1)) =
      Real.log δ / ((2 : ℝ) ^ N) := by
  subst δnext
  have hδ_ne : δ ≠ 0 := ne_of_gt hδ
  have hden_ne : ((2 : ℝ) ^ N) ≠ 0 := by
    exact pow_ne_zero N (by norm_num)
  have htwo_ne : (2 : ℝ) ≠ 0 := by
    norm_num
  have hden_mul_ne : (((2 : ℝ) ^ N) * 2) ≠ 0 := by
    exact mul_ne_zero hden_ne htwo_ne
  have hden_succ :
      ((2 : ℝ) ^ (N + 1)) = ((2 : ℝ) ^ N) * 2 := by
    simpa using (pow_succ (2 : ℝ) N)
  calc
    Real.log (δ ^ 2) / ((2 : ℝ) ^ (N + 1))
        = Real.log (δ * δ) / (((2 : ℝ) ^ N) * 2) := by
            rw [show δ ^ 2 = δ * δ by ring]
            rw [hden_succ]
    _ = (Real.log δ + Real.log δ) / (((2 : ℝ) ^ N) * 2) := by
            rw [Real.log_mul hδ_ne hδ_ne]
    _ = Real.log δ / ((2 : ℝ) ^ N) := by
            field_simp [hden_ne, hden_mul_ne]
            ring

/--
Stage-function version of normalized log-determinant stabilization.

Use this when a finite tower has determinant values `detStage N` and the
bonding step satisfies `detStage (N+1) = detStage N ^ 2`.
-/
theorem normalized_logdet_stage_stable
    (detStage : ℕ → ℝ)
    (N : ℕ)
    (hpos : 0 < detStage N)
    (hsquare : detStage (N + 1) = detStage N ^ 2) :
    Real.log (detStage (N + 1)) / ((2 : ℝ) ^ (N + 1)) =
      Real.log (detStage N) / ((2 : ℝ) ^ N) :=
  normalized_logdet_stable_of_square
    (δ := detStage N)
    (δnext := detStage (N + 1))
    (N := N)
    hpos
    hsquare

namespace ZornCell

variable {V : Type*}
variable [AddCommGroup V] [Module ℝ V]

/-- Negative logarithmic Zorn determinant potential. -/
def zornLogBarrier
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X : ZornCell ℝ V) : ℝ :=
  - Real.log (ZornCell.detZ B X)

/--
Radon--Nikodym-style relative Zorn volume factor:

  RN(X,Y) = detZ(Y) / detZ(X).
-/
def zornRelativeVolumeRN
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X Y : ZornCell ℝ V) : ℝ :=
  ZornCell.detZ B Y / ZornCell.detZ B X

/-- Coercion of a real unit is nonzero. -/
private lemma unit_coe_ne_zero (u : ℝˣ) :
    (u : ℝ) ≠ 0 :=
  Units.ne_zero u

/--
The determinant remains positive under componentwise unit scaling.

This is the domain-preservation theorem for the positive log-volume chart.
-/
theorem detZ_scalarScale_pos
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u : ℝˣ) (X : ZornCell ℝ V)
    (hX : 0 < ZornCell.detZ B X) :
    0 < ZornCell.detZ B (ZornCell.scalarScale u X) := by
  rw [ZornCell.detZ_scalarScale]
  exact mul_pos (sq_pos_of_ne_zero (unit_coe_ne_zero u)) hX

/--
Log-barrier shift under Zorn unit scaling.

Since

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
The relative Zorn volume of a point with itself is `1`
on the non-isotropic stratum.
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
    (u : ℝˣ) (X Y : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0) :
    zornRelativeVolumeRN B X (ZornCell.scalarScale u Y)
      =
    ((u : ℝ) ^ 2) * zornRelativeVolumeRN B X Y := by
  unfold zornRelativeVolumeRN
  rw [ZornCell.detZ_scalarScale]
  field_simp [hX]

/--
Left scaling of the base divides the relative-volume factor by `u²`.
-/
theorem zornRelativeVolumeRN_scalarScale_left
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u : ℝˣ) (X Y : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0) :
    zornRelativeVolumeRN B (ZornCell.scalarScale u X) Y
      =
    (((u : ℝ) ^ 2)⁻¹) * zornRelativeVolumeRN B X Y := by
  unfold zornRelativeVolumeRN
  rw [ZornCell.detZ_scalarScale]
  field_simp [hX, pow_ne_zero 2 (unit_coe_ne_zero u)]

/--
If the Zorn determinant scales by `u²`, then the induced 8-dimensional
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
The negative logarithm of the Zorn scale Jacobian can be rewritten using
the simplified eighth-power form.
-/
theorem negLog_zornVolumeJacobianOfScale
    (u : ℝˣ) :
    - Real.log (zornVolumeJacobianOfScale u)
      =
    - Real.log ((u : ℝ) ^ 8) := by
  rw [zornVolumeJacobianOfScale_eq_pow_eight u]

end ZornCell

end

end InfoGeometry.Projective.SplitOctonions
