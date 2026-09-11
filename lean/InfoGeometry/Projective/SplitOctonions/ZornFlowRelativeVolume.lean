import InfoGeometry.Projective.SplitOctonions.ZornLogVolume
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Zorn determinant-similitude flow relative volume

This file promotes the theorem-honest algebraic part of the Zorn flow/RN
sandbox to the projective split-octonion owner lane.

It only formalizes determinant-ratio relative-volume factors and determinant
similitudes of the existing local Zorn determinant.  It does not assert a
smooth Radon--Nikodym derivative, a full structure group, Tomita--Takesaki
modular theory, Super-Kähler geometry, or a global `G₂` automorphism theorem.
-/

namespace InfoGeometry.Projective.SplitOctonions

noncomputable section

namespace ZornCell

variable {V : Type*}
variable [AddCommGroup V] [Module ℝ V]

/--
Determinant-ratio relative-volume factor attached to a pair of Zorn cells.

This is the same algebraic object as `zornRelativeVolumeRN`; the name records
its intended use for a finite flow step `X ↦ Y`.
-/
def flowRelativeVolumeRN
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X Y : ZornCell ℝ V) : ℝ :=
  ZornCell.detZ B Y / ZornCell.detZ B X

/-- `flowRelativeVolumeRN` is definitionally the existing Zorn RN-style factor. -/
theorem flowRelativeVolumeRN_eq_zornRelativeVolumeRN
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X Y : ZornCell ℝ V) :
    flowRelativeVolumeRN B X Y = zornRelativeVolumeRN B X Y :=
  rfl

/-- A map preserves the local Zorn determinant. -/
def DetPreserving
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Φ : ZornCell ℝ V → ZornCell ℝ V) : Prop :=
  ∀ X, ZornCell.detZ B (Φ X) = ZornCell.detZ B X

/-- A map is a determinant similitude with multiplier `χ`. -/
def DetSimilitude
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Φ : ZornCell ℝ V → ZornCell ℝ V)
    (χ : ℝ) : Prop :=
  ∀ X, ZornCell.detZ B (Φ X) = χ * ZornCell.detZ B X

/-- The identity flow has relative-volume factor `1` on the non-isotropic stratum. -/
theorem flowRelativeVolumeRN_self
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0) :
    flowRelativeVolumeRN B X X = 1 := by
  exact zornRelativeVolumeRN_self B X hX

/-- Alias for the identity-flow formulation of `flowRelativeVolumeRN_self`. -/
theorem flowRelativeVolumeRN_id
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0) :
    flowRelativeVolumeRN B X (id X) = 1 := by
  simpa using flowRelativeVolumeRN_self B X hX

/--
Determinant-ratio cocycle:

`RN(X,Z) = RN(X,Y) * RN(Y,Z)`

whenever the base and intermediate determinants are nonzero.
-/
theorem flowRelativeVolumeRN_comp
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X Y Z : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0)
    (hY : ZornCell.detZ B Y ≠ 0) :
    flowRelativeVolumeRN B X Z =
      flowRelativeVolumeRN B X Y * flowRelativeVolumeRN B Y Z := by
  unfold flowRelativeVolumeRN
  field_simp [hX, hY]

/--
The negative logarithm of the flow relative-volume factor is the difference of
Zorn log-barrier potentials.
-/
theorem zornLogBarrier_flowDifference
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X Y : ZornCell ℝ V)
    (hX : 0 < ZornCell.detZ B X)
    (hY : 0 < ZornCell.detZ B Y) :
    - Real.log (flowRelativeVolumeRN B X Y) =
      zornLogBarrier B Y - zornLogBarrier B X := by
  exact negLog_zornRelativeVolumeRN_eq_zornLogBarrier_sub B X Y (ne_of_gt hX) (ne_of_gt hY)

/-- The identity map preserves the Zorn determinant. -/
theorem detPreserving_id
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    DetPreserving B id :=
  fun _ => rfl

/-- A determinant-preserving map is a determinant similitude with multiplier `1`. -/
theorem detSimilitude_one_of_detPreserving
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Φ : ZornCell ℝ V → ZornCell ℝ V)
    (h : DetPreserving B Φ) :
    DetSimilitude B Φ 1 := by
  intro X
  rw [h X, one_mul]

/-- The identity map is a determinant similitude with multiplier `1`. -/
theorem detSimilitude_id
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) :
    DetSimilitude B id 1 :=
  detSimilitude_one_of_detPreserving B id (detPreserving_id B)

/-- Determinant-preserving maps are closed under composition. -/
theorem detPreserving_comp
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Φ Ψ : ZornCell ℝ V → ZornCell ℝ V)
    (hΦ : DetPreserving B Φ)
    (hΨ : DetPreserving B Ψ) :
    DetPreserving B (Ψ ∘ Φ) := by
  intro X
  simp only [Function.comp_apply]
  rw [hΨ, hΦ]

/-- Determinant similitudes compose, multiplying their characters. -/
theorem detSimilitude_comp
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Φ Ψ : ZornCell ℝ V → ZornCell ℝ V)
    (χ ψ : ℝ)
    (hΦ : DetSimilitude B Φ χ)
    (hΨ : DetSimilitude B Ψ ψ) :
    DetSimilitude B (Ψ ∘ Φ) (ψ * χ) := by
  intro X
  simp only [Function.comp_apply]
  rw [hΨ, hΦ]
  ring

/-- A positive-multiplier similitude preserves the positive determinant stratum. -/
theorem detSimilitude_pos
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Φ : ZornCell ℝ V → ZornCell ℝ V)
    (χ : ℝ)
    (hΦ : DetSimilitude B Φ χ)
    (hχ : 0 < χ)
    (X : ZornCell ℝ V)
    (hX : 0 < ZornCell.detZ B X) :
    0 < ZornCell.detZ B (Φ X) := by
  rw [hΦ X]
  exact mul_pos hχ hX

/--
For a positive-multiplier determinant similitude, the log barrier shifts by
`-log χ` on the positive determinant stratum.
-/
theorem zornLogBarrier_detSimilitude
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Φ : ZornCell ℝ V → ZornCell ℝ V)
    (χ : ℝ)
    (hΦ : DetSimilitude B Φ χ)
    (hχ : 0 < χ)
    (X : ZornCell ℝ V)
    (hX : 0 < ZornCell.detZ B X) :
    zornLogBarrier B (Φ X) = zornLogBarrier B X - Real.log χ := by
  unfold zornLogBarrier
  rw [hΦ X]
  rw [Real.log_mul (ne_of_gt hχ) (ne_of_gt hX)]
  ring

/-- A determinant similitude has RN-style factor equal to its multiplier. -/
theorem RN_of_detSimilitude
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Φ : ZornCell ℝ V → ZornCell ℝ V)
    (χ : ℝ)
    (hΦ : DetSimilitude B Φ χ)
    (X : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0) :
    flowRelativeVolumeRN B X (Φ X) = χ := by
  unfold flowRelativeVolumeRN
  rw [hΦ X]
  field_simp [hX]

/-- A determinant-preserving map has RN-style factor `1`. -/
theorem RN_of_detPreserving
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Φ : ZornCell ℝ V → ZornCell ℝ V)
    (hΦ : DetPreserving B Φ)
    (X : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0) :
    flowRelativeVolumeRN B X (Φ X) = 1 := by
  exact RN_of_detSimilitude B Φ 1
    (detSimilitude_one_of_detPreserving B Φ hΦ) X hX

/-- Componentwise unit scaling is a determinant similitude with multiplier `u²`. -/
theorem detSimilitude_scalarScale
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u : ℝˣ) :
    DetSimilitude B (ZornCell.scalarScale u) ((u : ℝ) ^ 2) := by
  intro X
  exact ZornCell.detZ_scalarScale B u X

/-- The RN-style factor of componentwise unit scaling is `u²`. -/
theorem RN_scalarScale_from_detSimilitude
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u : ℝˣ)
    (X : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0) :
    flowRelativeVolumeRN B X (ZornCell.scalarScale u X) = (u : ℝ) ^ 2 := by
  exact RN_of_detSimilitude B (ZornCell.scalarScale u) ((u : ℝ) ^ 2)
    (detSimilitude_scalarScale B u) X hX

/--
Generic scalar/similitude-step form: if `scaledX` has determinant
`χ * detZ X`, then the flow RN-style factor from `X` to `scaledX` is `χ`.
-/
theorem flowRelativeVolumeRN_of_det_scale
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X scaledX : ZornCell ℝ V)
    (χ : ℝ)
    (hX : ZornCell.detZ B X ≠ 0)
    (h_scale : ZornCell.detZ B scaledX = χ * ZornCell.detZ B X) :
    flowRelativeVolumeRN B X scaledX = χ := by
  unfold flowRelativeVolumeRN
  rw [h_scale]
  field_simp [hX]

/--
Compatibility name for the scalar-scaling packet: a step whose determinant is
scaled by `u²` has RN-style factor `u²`.
-/
theorem flowRelativeVolumeRN_scalarScale
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X scaledX : ZornCell ℝ V)
    (u : ℝ)
    (hX : ZornCell.detZ B X ≠ 0)
    (h_scale : ZornCell.detZ B scaledX = u ^ 2 * ZornCell.detZ B X) :
    flowRelativeVolumeRN B X scaledX = u ^ 2 :=
  flowRelativeVolumeRN_of_det_scale B X scaledX (u ^ 2) hX h_scale

/--
If two points have the same Zorn determinant, their determinant-ratio
relative-volume factor is `1`.
-/
theorem flowRelativeVolumeRN_det_preserving
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X Y : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0)
    (h_pres : ZornCell.detZ B Y = ZornCell.detZ B X) :
    flowRelativeVolumeRN B X Y = 1 := by
  unfold flowRelativeVolumeRN
  rw [h_pres]
  field_simp [hX]

/-- Right scaling of the target multiplies the flow RN-style factor by `u²`. -/
theorem flowRelativeVolumeRN_scalarScale_right
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u : ℝˣ) (X Y : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0) :
    flowRelativeVolumeRN B X (ZornCell.scalarScale u Y) =
      ((u : ℝ) ^ 2) * flowRelativeVolumeRN B X Y := by
  exact zornRelativeVolumeRN_scalarScale_right B u X Y hX

/-- Left scaling of the base divides the flow RN-style factor by `u²`. -/
theorem flowRelativeVolumeRN_scalarScale_left
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u : ℝˣ) (X Y : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0) :
    flowRelativeVolumeRN B (ZornCell.scalarScale u X) Y =
      (((u : ℝ) ^ 2)⁻¹) * flowRelativeVolumeRN B X Y := by
  exact zornRelativeVolumeRN_scalarScale_left B u X Y hX

/-- Simultaneous unit scaling of base and target leaves the RN-style factor unchanged. -/
theorem flowRelativeVolumeRN_scalarScale_both
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u : ℝˣ) (X Y : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0) :
    flowRelativeVolumeRN B (ZornCell.scalarScale u X) (ZornCell.scalarScale u Y) =
      flowRelativeVolumeRN B X Y := by
  unfold flowRelativeVolumeRN
  rw [ZornCell.detZ_scalarScale, ZornCell.detZ_scalarScale]
  field_simp [hX, pow_ne_zero 2 (Units.ne_zero u)]

/--
Combined relative density for a finite flow step.

The factor `jacobian X` is intentionally external: it represents an ambient
coordinate-volume Jacobian.  The Zorn determinant contributes only the internal
relative factor `flowRelativeVolumeRN B X (Φ X)`.
-/
def totalFlowRelativeDensity
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Φ : ZornCell ℝ V → ZornCell ℝ V)
    (jacobian : ZornCell ℝ V → ℝ)
    (X : ZornCell ℝ V) : ℝ :=
  jacobian X * flowRelativeVolumeRN B X (Φ X)

/-- With unit ambient Jacobian, the identity flow has combined density `1`. -/
theorem totalFlowRelativeDensity_id_one
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (X : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0) :
    totalFlowRelativeDensity B id (fun _ => 1) X = 1 := by
  unfold totalFlowRelativeDensity
  simpa using flowRelativeVolumeRN_self B X hX

/--
For a determinant similitude, the internal determinant-density contribution is
the multiplier `χ`; the ambient Jacobian remains a separate factor.
-/
theorem totalFlowRelativeDensity_of_detSimilitude
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Φ : ZornCell ℝ V → ZornCell ℝ V)
    (jacobian : ZornCell ℝ V → ℝ)
    (χ : ℝ)
    (hΦ : DetSimilitude B Φ χ)
    (X : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0) :
    totalFlowRelativeDensity B Φ jacobian X = jacobian X * χ := by
  unfold totalFlowRelativeDensity
  rw [RN_of_detSimilitude B Φ χ hΦ X hX]

/-- A determinant-preserving flow contributes no internal Zorn density factor. -/
theorem totalFlowRelativeDensity_of_detPreserving
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (Φ : ZornCell ℝ V → ZornCell ℝ V)
    (jacobian : ZornCell ℝ V → ℝ)
    (hΦ : DetPreserving B Φ)
    (X : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0) :
    totalFlowRelativeDensity B Φ jacobian X = jacobian X := by
  rw [totalFlowRelativeDensity_of_detSimilitude
    B Φ jacobian 1 (detSimilitude_one_of_detPreserving B Φ hΦ) X hX]
  ring

/--
For scalar scaling, the combined density separates into the ambient
8-dimensional Jacobian factor and the internal determinant character `u²`.
-/
theorem totalFlowRelativeDensity_scalarScale_zornJacobian
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u : ℝˣ)
    (X : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0) :
    totalFlowRelativeDensity B (ZornCell.scalarScale u)
        (fun _ => zornVolumeJacobianOfScale u) X =
      zornVolumeJacobianOfScale u * ((u : ℝ) ^ 2) := by
  exact totalFlowRelativeDensity_of_detSimilitude
    B (ZornCell.scalarScale u) (fun _ => zornVolumeJacobianOfScale u)
    ((u : ℝ) ^ 2) (detSimilitude_scalarScale B u) X hX

/--
The scalar-scaling combined density can also be written with the ambient
Jacobian displayed as `u^8`.
-/
theorem totalFlowRelativeDensity_scalarScale_pow_eight
    (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (u : ℝˣ)
    (X : ZornCell ℝ V)
    (hX : ZornCell.detZ B X ≠ 0) :
    totalFlowRelativeDensity B (ZornCell.scalarScale u)
        (fun _ => zornVolumeJacobianOfScale u) X =
      ((u : ℝ) ^ 8) * ((u : ℝ) ^ 2) := by
  rw [totalFlowRelativeDensity_scalarScale_zornJacobian B u X hX,
    zornVolumeJacobianOfScale_eq_pow_eight]

end ZornCell

end

end InfoGeometry.Projective.SplitOctonions
