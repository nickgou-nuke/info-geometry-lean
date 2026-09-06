import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Abstract determinant-ratio flow relative volume

This file is a small abstract sandbox for the determinant-ratio RN algebra used
by the concrete Zorn owner file
`InfoGeometry.Projective.SplitOctonions.ZornFlowRelativeVolume`.

It is intentionally over `ℝ`, since the log-barrier statements use `Real.log`.
The production Zorn definitions remain in the concrete owner file.
-/

namespace InfoGeometry.Projective.SplitOctonions.ZornFlowRelativeVolumeAbstract

noncomputable section

variable {ZornMatrix BilinearForm : Type*}

/-- Radon--Nikodym-style relative volume of a flow step computed by determinant ratio. -/
def flowRelativeVolumeRN
    (detZ : BilinearForm → ZornMatrix → ℝ)
    (B : BilinearForm) (X Y : ZornMatrix) : ℝ :=
  detZ B Y / detZ B X

/-- A map preserves the determinant. -/
def DetPreserving
    (detZ : BilinearForm → ZornMatrix → ℝ)
    (B : BilinearForm) (Φ : ZornMatrix → ZornMatrix) : Prop :=
  ∀ X, detZ B (Φ X) = detZ B X

/-- A map is a determinant similitude with multiplier `χ`. -/
def DetSimilitude
    (detZ : BilinearForm → ZornMatrix → ℝ)
    (B : BilinearForm) (Φ : ZornMatrix → ZornMatrix) (χ : ℝ) : Prop :=
  ∀ X, detZ B (Φ X) = χ * detZ B X

/-- Determinant-ratio cocycle: `RN(X,Z) = RN(X,Y) * RN(Y,Z)`. -/
theorem flowRelativeVolumeRN_comp
    (detZ : BilinearForm → ZornMatrix → ℝ)
    (B : BilinearForm) (X Y Z : ZornMatrix)
    (hX : detZ B X ≠ 0) (hY : detZ B Y ≠ 0) :
    flowRelativeVolumeRN detZ B X Z =
      flowRelativeVolumeRN detZ B X Y * flowRelativeVolumeRN detZ B Y Z := by
  unfold flowRelativeVolumeRN
  field_simp [hX, hY]

/-- The identity map preserves the determinant. -/
theorem detPreserving_id
    (detZ : BilinearForm → ZornMatrix → ℝ)
    (B : BilinearForm) :
    DetPreserving detZ B id :=
  fun _ => rfl

/-- A determinant-preserving map is a determinant similitude with multiplier `1`. -/
theorem detSimilitude_one_of_detPreserving
    (detZ : BilinearForm → ZornMatrix → ℝ)
    (B : BilinearForm) (Φ : ZornMatrix → ZornMatrix)
    (h : DetPreserving detZ B Φ) :
    DetSimilitude detZ B Φ 1 := by
  intro X
  rw [h X, one_mul]

/-- A determinant similitude has RN-style factor equal to its multiplier. -/
theorem RN_of_detSimilitude
    (detZ : BilinearForm → ZornMatrix → ℝ)
    (B : BilinearForm) (Φ : ZornMatrix → ZornMatrix) (χ : ℝ)
    (hΦ : DetSimilitude detZ B Φ χ)
    (X : ZornMatrix) (hX : detZ B X ≠ 0) :
    flowRelativeVolumeRN detZ B X (Φ X) = χ := by
  unfold flowRelativeVolumeRN
  rw [hΦ X]
  field_simp [hX]

/-- A determinant-preserving map has RN-style factor `1`. -/
theorem RN_of_detPreserving
    (detZ : BilinearForm → ZornMatrix → ℝ)
    (B : BilinearForm) (Φ : ZornMatrix → ZornMatrix)
    (hΦ : DetPreserving detZ B Φ)
    (X : ZornMatrix) (hX : detZ B X ≠ 0) :
    flowRelativeVolumeRN detZ B X (Φ X) = 1 := by
  exact RN_of_detSimilitude detZ B Φ 1
    (detSimilitude_one_of_detPreserving detZ B Φ hΦ) X hX

/-- A determinant scaling law produces the corresponding RN-style factor. -/
theorem flowRelativeVolumeRN_of_det_scale
    (detZ : BilinearForm → ZornMatrix → ℝ)
    (B : BilinearForm) (X scaledX : ZornMatrix) (χ : ℝ)
    (hX : detZ B X ≠ 0)
    (h_scale : detZ B scaledX = χ * detZ B X) :
    flowRelativeVolumeRN detZ B X scaledX = χ := by
  unfold flowRelativeVolumeRN
  rw [h_scale]
  field_simp [hX]

/-- Scalar-scaling compatibility when the determinant scales by `u^2`. -/
theorem flowRelativeVolumeRN_scalarScale
    (detZ : BilinearForm → ZornMatrix → ℝ)
    (scalarScale : ℝ → ZornMatrix → ZornMatrix)
    (h_scalar_scale_det :
      ∀ (B : BilinearForm) (u : ℝ) (X : ZornMatrix),
        detZ B (scalarScale u X) = u ^ 2 * detZ B X)
    (B : BilinearForm) (u : ℝ) (X : ZornMatrix)
    (hX : detZ B X ≠ 0) :
    flowRelativeVolumeRN detZ B X (scalarScale u X) = u ^ 2 :=
  flowRelativeVolumeRN_of_det_scale detZ B X (scalarScale u X) (u ^ 2)
    hX (h_scalar_scale_det B u X)

/--
The negative log of the determinant-ratio RN factor is the difference of
log-barrier potentials, assuming the supplied barrier is `-log detZ`.
-/
theorem zornLogBarrier_flowDifference
    (detZ : BilinearForm → ZornMatrix → ℝ)
    (zornLogBarrier : BilinearForm → ZornMatrix → ℝ)
    (h_log_barrier :
      ∀ B X, 0 < detZ B X → zornLogBarrier B X = - Real.log (detZ B X))
    (B : BilinearForm) (X Y : ZornMatrix)
    (hX : 0 < detZ B X) (hY : 0 < detZ B Y) :
    - Real.log (flowRelativeVolumeRN detZ B X Y) =
      zornLogBarrier B Y - zornLogBarrier B X := by
  unfold flowRelativeVolumeRN
  rw [h_log_barrier B X hX, h_log_barrier B Y hY]
  rw [Real.log_div (ne_of_gt hY) (ne_of_gt hX)]
  ring

end

end InfoGeometry.Projective.SplitOctonions.ZornFlowRelativeVolumeAbstract
