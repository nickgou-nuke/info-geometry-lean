
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

open Matrix

namespace AmplituhedronVolumeForm

/-! ### Four-variable scalar chart model

This file defines scalar coordinate maps and reciprocal-product coefficients.
It does not construct differential forms, the Plabic boundary measurement
map, or an amplituhedron canonical form. -/

/-- Four positive scalar coordinates used by this finite chart model. -/
structure PlabicWeights where
  t₁ : ℝ
  t₂ : ℝ
  t₃ : ℝ
  t₄ : ℝ
  pos₁ : 0 < t₁
  pos₂ : 0 < t₂
  pos₃ : 0 < t₃
  pos₄ : 0 < t₄

/-- Four scalar slots for the chart's bracket-like coordinates. -/
structure FacetBrackets where
  B₀₁ : ℝ
  B₁₂ : ℝ
  B₂₃ : ℝ
  B₀₃ : ℝ

/-- The chosen diagonal scalar map from four chart coordinates and one scale
parameter to four scalar slots. -/
def weightsToBrackets (w : PlabicWeights) (detZ : ℝ) : FacetBrackets :=
  { B₀₁ := w.t₄ * detZ
    B₁₂ := w.t₃ * detZ
    B₂₃ := w.t₂ * detZ
    B₀₃ := w.t₁ * detZ }

/-! ### 2. Reciprocal-product coefficients -/

/-- Reciprocal-product coefficient for four positive chart coordinates. -/
noncomputable def dlogCellDensity (w : PlabicWeights) : ℝ :=
  1 / (w.t₁ * w.t₂ * w.t₃ * w.t₄)

/-- Reciprocal-product coefficient for the four scalar bracket slots. -/
noncomputable def dlogAmplituhedronDensity (B : FacetBrackets) : ℝ :=
  1 / (B.B₀₁ * B.B₁₂ * B.B₂₃ * B.B₀₃)

/-- Determinant of the diagonal linear map specified by `weightsToBrackets`. -/
def jacobianDet (detZ : ℝ) : ℝ :=
  detZ ^ 4

/-! ### 3. Exact Jacobian Cancellation & Pullback Invariance -/

lemma weights_prod_pos (w : PlabicWeights) : 0 < w.t₁ * w.t₂ * w.t₃ * w.t₄ :=
  mul_pos (mul_pos (mul_pos w.pos₁ w.pos₂) w.pos₃) w.pos₄

lemma weights_prod_ne_zero (w : PlabicWeights) : w.t₁ * w.t₂ * w.t₃ * w.t₄ ≠ 0 :=
  ne_of_gt (weights_prod_pos w)

lemma detZ_pow_four_ne_zero {detZ : ℝ} (hZ : 0 < detZ) : detZ ^ 4 ≠ 0 :=
  pow_ne_zero 4 (ne_of_gt hZ)

/-- For the specified diagonal scalar map, its determinant cancels the
reciprocal-product scale in these coefficient functions. -/
theorem amplituhedron_volume_form_pullback (w : PlabicWeights) {detZ : ℝ} (hZ : 0 < detZ) :
    dlogAmplituhedronDensity (weightsToBrackets w detZ) * jacobianDet detZ =
      dlogCellDensity w := by
  dsimp [dlogAmplituhedronDensity, dlogCellDensity, weightsToBrackets, jacobianDet]
  have h_prod : (w.t₄ * detZ) * (w.t₃ * detZ) * (w.t₂ * detZ) * (w.t₁ * detZ) =
      (w.t₁ * w.t₂ * w.t₃ * w.t₄) * detZ ^ 4 := by ring
  rw [h_prod]
  have hW := weights_prod_ne_zero w
  have hZ4 := detZ_pow_four_ne_zero hZ
  field_simp

/-! ### 4. Logarithmic Residues along Physical Boundaries -/

/-- Reciprocal-product coefficient after omitting coordinate `t₁`. -/
noncomputable def boundaryResidue1 (w : PlabicWeights) : ℝ :=
  1 / (w.t₂ * w.t₃ * w.t₄)

/-- Reciprocal-product coefficient after omitting coordinate `t₂`. -/
noncomputable def boundaryResidue2 (w : PlabicWeights) : ℝ :=
  1 / (w.t₁ * w.t₃ * w.t₄)

/-- Reciprocal-product coefficient after omitting coordinate `t₃`. -/
noncomputable def boundaryResidue3 (w : PlabicWeights) : ℝ :=
  1 / (w.t₁ * w.t₂ * w.t₄)

/-- Reciprocal-product coefficient after omitting coordinate `t₄`. -/
noncomputable def boundaryResidue4 (w : PlabicWeights) : ℝ :=
  1 / (w.t₁ * w.t₂ * w.t₃)

/-- Interior coefficient identity obtained by multiplying by `t₁`; this does
not evaluate a boundary residue at `t₁ = 0`. -/
theorem residue_facet_1 (w : PlabicWeights) :
    dlogCellDensity w * w.t₁ = boundaryResidue1 w := by
  dsimp [dlogCellDensity, boundaryResidue1]
  have h1 : w.t₁ ≠ 0 := ne_of_gt w.pos₁
  have h234 : w.t₂ * w.t₃ * w.t₄ ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos w.pos₂ w.pos₃) w.pos₄)
  have h_split : w.t₁ * w.t₂ * w.t₃ * w.t₄ = w.t₁ * (w.t₂ * w.t₃ * w.t₄) := by ring
  rw [h_split]
  field_simp

/-- Interior coefficient identity obtained by multiplying by `t₂`; this does
not evaluate a boundary residue at `t₂ = 0`. -/
theorem residue_facet_2 (w : PlabicWeights) :
    dlogCellDensity w * w.t₂ = boundaryResidue2 w := by
  dsimp [dlogCellDensity, boundaryResidue2]
  have h2 : w.t₂ ≠ 0 := ne_of_gt w.pos₂
  have h134 : w.t₁ * w.t₃ * w.t₄ ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos w.pos₁ w.pos₃) w.pos₄)
  have h_split : w.t₁ * w.t₂ * w.t₃ * w.t₄ = w.t₂ * (w.t₁ * w.t₃ * w.t₄) := by ring
  rw [h_split]
  field_simp

/-- Interior coefficient identity obtained by multiplying by `t₃`; this does
not evaluate a boundary residue at `t₃ = 0`. -/
theorem residue_facet_3 (w : PlabicWeights) :
    dlogCellDensity w * w.t₃ = boundaryResidue3 w := by
  dsimp [dlogCellDensity, boundaryResidue3]
  have h3 : w.t₃ ≠ 0 := ne_of_gt w.pos₃
  have h124 : w.t₁ * w.t₂ * w.t₄ ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos w.pos₁ w.pos₂) w.pos₄)
  have h_split : w.t₁ * w.t₂ * w.t₃ * w.t₄ = w.t₃ * (w.t₁ * w.t₂ * w.t₄) := by ring
  rw [h_split]
  field_simp

/-- Interior coefficient identity obtained by multiplying by `t₄`; this does
not evaluate a boundary residue at `t₄ = 0`. -/
theorem residue_facet_4 (w : PlabicWeights) :
    dlogCellDensity w * w.t₄ = boundaryResidue4 w := by
  dsimp [dlogCellDensity, boundaryResidue4]
  have h4 : w.t₄ ≠ 0 := ne_of_gt w.pos₄
  have h123 : w.t₁ * w.t₂ * w.t₃ ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos w.pos₁ w.pos₂) w.pos₃)
  have h_split : w.t₁ * w.t₂ * w.t₃ * w.t₄ = w.t₄ * (w.t₁ * w.t₂ * w.t₃) := by ring
  rw [h_split]
  field_simp

/-! ### 5. Tree Scattering Amplitude Rational Function -/

/-- A rational scalar formed from the supplied scale and bracket-like slots.
No scattering-amplitude interpretation is formalized here. -/
noncomputable def treeScatteringAmplitude (B : FacetBrackets) (detZ : ℝ) : ℝ :=
  detZ ^ 2 / (B.B₀₁ * B.B₁₂ * B.B₂₃ * B.B₀₃)

/-- Evaluation of the rational scalar under `weightsToBrackets`. -/
theorem treeScatteringAmplitude_eval (w : PlabicWeights) {detZ : ℝ} (hZ : 0 < detZ) :
    treeScatteringAmplitude (weightsToBrackets w detZ) detZ =
      (1 / detZ ^ 2) * (1 / (w.t₁ * w.t₂ * w.t₃ * w.t₄)) := by
  dsimp [treeScatteringAmplitude, weightsToBrackets]
  have h_prod : (w.t₄ * detZ) * (w.t₃ * detZ) * (w.t₂ * detZ) * (w.t₁ * detZ) =
      (w.t₁ * w.t₂ * w.t₃ * w.t₄) * detZ ^ 4 := by ring
  rw [h_prod]
  have hW := weights_prod_ne_zero w
  have hZ2 : detZ ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hZ)
  have hZ4 : detZ ^ 4 ≠ 0 := pow_ne_zero 4 (ne_of_gt hZ)
  field_simp

end AmplituhedronVolumeForm
