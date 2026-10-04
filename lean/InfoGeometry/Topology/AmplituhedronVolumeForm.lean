
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Tactic

open Matrix

namespace AmplituhedronVolumeForm

/-! ### 1. Plabic Graph Weights & Boundary Brackets -/

/-- Positive face/edge weights parameterizing the top cell of Gr_{>0}(2, 4). -/
structure PlabicWeights where
  t₁ : ℝ
  t₂ : ℝ
  t₃ : ℝ
  t₄ : ℝ
  pos₁ : 0 < t₁
  pos₂ : 0 < t₂
  pos₃ : 0 < t₃
  pos₄ : 0 < t₄

/-- The four physical boundary 4-brackets B_i = ⟨Y Z_i Z_{i+1}⟩ on the Amplituhedron. -/
structure FacetBrackets where
  B₀₁ : ℝ
  B₁₂ : ℝ
  B₂₃ : ℝ
  B₀₃ : ℝ

/-- Mapping from plabic graph weights and external twistor determinant to facet brackets:
    B₀₁ = t₄ * det(Z)
    B₁₂ = t₃ * det(Z)
    B₂₃ = t₂ * det(Z)
    B₀₃ = t₁ * det(Z). -/
def weightsToBrackets (w : PlabicWeights) (detZ : ℝ) : FacetBrackets :=
  { B₀₁ := w.t₄ * detZ
    B₁₂ := w.t₃ * detZ
    B₂₃ := w.t₂ * detZ
    B₀₃ := w.t₁ * detZ }

/-! ### 2. Differential Form Densities -/

/-- The dlog volume form density on the positive Grassmannian cell:
    ω_{cell} = (1 / (t₁ t₂ t₃ t₄)) dt₁ ∧ dt₂ ∧ dt₃ ∧ dt₄. -/
noncomputable def dlogCellDensity (w : PlabicWeights) : ℝ :=
  1 / (w.t₁ * w.t₂ * w.t₃ * w.t₄)

/-- The dlog volume form density on the Amplituhedron twistor space:
    Ω = (1 / (B₀₁ B₁₂ B₂₃ B₀₃)) dB₀₁ ∧ dB₁₂ ∧ dB₂₃ ∧ dB₀₃. -/
noncomputable def dlogAmplituhedronDensity (B : FacetBrackets) : ℝ :=
  1 / (B.B₀₁ * B.B₁₂ * B.B₂₃ * B.B₀₃)

/-- The Jacobian determinant of the change of variables t ↦ B:
    det(∂B / ∂t) = det(Z)⁴. -/
def jacobianDet (detZ : ℝ) : ℝ :=
  detZ ^ 4

/-! ### 3. Exact Jacobian Cancellation & Pullback Invariance -/

lemma weights_prod_pos (w : PlabicWeights) : 0 < w.t₁ * w.t₂ * w.t₃ * w.t₄ :=
  mul_pos (mul_pos (mul_pos w.pos₁ w.pos₂) w.pos₃) w.pos₄

lemma weights_prod_ne_zero (w : PlabicWeights) : w.t₁ * w.t₂ * w.t₃ * w.t₄ ≠ 0 :=
  ne_of_gt (weights_prod_pos w)

lemma detZ_pow_four_ne_zero {detZ : ℝ} (hZ : 0 < detZ) : detZ ^ 4 ≠ 0 :=
  pow_ne_zero 4 (ne_of_gt hZ)

/-- Core Theorem: The logarithmic volume form on the Amplituhedron pulls back
    identically to the canonical dlog volume form on the positive Grassmannian cell.
    The external twistor scale det(Z)⁴ cancels identically between the poles and the Jacobian. -/
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

/-- The 3-dimensional boundary volume form on Facet 1 (t₁ → 0 / B₀₃ → 0). -/
noncomputable def boundaryResidue1 (w : PlabicWeights) : ℝ :=
  1 / (w.t₂ * w.t₃ * w.t₄)

/-- The 3-dimensional boundary volume form on Facet 2 (t₂ → 0 / B₂₃ → 0). -/
noncomputable def boundaryResidue2 (w : PlabicWeights) : ℝ :=
  1 / (w.t₁ * w.t₃ * w.t₄)

/-- The 3-dimensional boundary volume form on Facet 3 (t₃ → 0 / B₁₂ → 0). -/
noncomputable def boundaryResidue3 (w : PlabicWeights) : ℝ :=
  1 / (w.t₁ * w.t₂ * w.t₄)

/-- The 3-dimensional boundary volume form on Facet 4 (t₄ → 0 / B₀₁ → 0). -/
noncomputable def boundaryResidue4 (w : PlabicWeights) : ℝ :=
  1 / (w.t₁ * w.t₂ * w.t₃)

/-- Unit Residue Theorem on Facet 1: Res_{t₁ = 0} Ω = dlog(t₂) ∧ dlog(t₃) ∧ dlog(t₄). -/
theorem residue_facet_1 (w : PlabicWeights) :
    dlogCellDensity w * w.t₁ = boundaryResidue1 w := by
  dsimp [dlogCellDensity, boundaryResidue1]
  have h1 : w.t₁ ≠ 0 := ne_of_gt w.pos₁
  have h234 : w.t₂ * w.t₃ * w.t₄ ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos w.pos₂ w.pos₃) w.pos₄)
  have h_split : w.t₁ * w.t₂ * w.t₃ * w.t₄ = w.t₁ * (w.t₂ * w.t₃ * w.t₄) := by ring
  rw [h_split]
  field_simp

/-- Unit Residue Theorem on Facet 2: Res_{t₂ = 0} Ω = dlog(t₁) ∧ dlog(t₃) ∧ dlog(t₄). -/
theorem residue_facet_2 (w : PlabicWeights) :
    dlogCellDensity w * w.t₂ = boundaryResidue2 w := by
  dsimp [dlogCellDensity, boundaryResidue2]
  have h2 : w.t₂ ≠ 0 := ne_of_gt w.pos₂
  have h134 : w.t₁ * w.t₃ * w.t₄ ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos w.pos₁ w.pos₃) w.pos₄)
  have h_split : w.t₁ * w.t₂ * w.t₃ * w.t₄ = w.t₂ * (w.t₁ * w.t₃ * w.t₄) := by ring
  rw [h_split]
  field_simp

/-- Unit Residue Theorem on Facet 3: Res_{t₃ = 0} Ω = dlog(t₁) ∧ dlog(t₂) ∧ dlog(t₄). -/
theorem residue_facet_3 (w : PlabicWeights) :
    dlogCellDensity w * w.t₃ = boundaryResidue3 w := by
  dsimp [dlogCellDensity, boundaryResidue3]
  have h3 : w.t₃ ≠ 0 := ne_of_gt w.pos₃
  have h124 : w.t₁ * w.t₂ * w.t₄ ≠ 0 :=
    ne_of_gt (mul_pos (mul_pos w.pos₁ w.pos₂) w.pos₄)
  have h_split : w.t₁ * w.t₂ * w.t₃ * w.t₄ = w.t₃ * (w.t₁ * w.t₂ * w.t₄) := by ring
  rw [h_split]
  field_simp

/-- Unit Residue Theorem on Facet 4: Res_{t₄ = 0} Ω = dlog(t₁) ∧ dlog(t₂) ∧ dlog(t₃). -/
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

/-- The Parke-Taylor / Amplituhedron tree scattering amplitude rational factor:
    M₄ = det(Z)² / (B₀₁ B₁₂ B₂₃ B₀₃). -/
noncomputable def treeScatteringAmplitude (B : FacetBrackets) (detZ : ℝ) : ℝ :=
  detZ ^ 2 / (B.B₀₁ * B.B₁₂ * B.B₂₃ * B.B₀₃)

/-- Reduction to Plabic Face Variables:
    The scattering amplitude is independent of external scale up to the canonical
    homogeneous twistor weight -2 in each particle. -/
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
