import InfoGeometry.Krein.SplitQuadraticSheets
import InfoGeometry.Clifford.Grading
import InfoGeometry.Meta.Architecture

open scoped InnerProductSpace

namespace InfoGeometry.Krein.PolarizedSector

open InfoGeometry.Krein.SplitQuadraticSheets

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H2" => DoubledSpace E
local notation "Pplus" => spectralPlusProj (E := E)
local notation "Pminus" => spectralMinusProj (E := E)

omit [CompleteSpace E] in
private theorem half_smul_add_half_smul (z : E) :
    ((2 : ℝ)⁻¹) • z + ((2 : ℝ)⁻¹) • z = z := by
  calc
    ((2 : ℝ)⁻¹) • z + ((2 : ℝ)⁻¹) • z
        = (((2 : ℝ)⁻¹ + (2 : ℝ)⁻¹) : ℝ) • z := by
            simpa using (add_smul ((2 : ℝ)⁻¹) ((2 : ℝ)⁻¹) z).symm
    _ = z := by norm_num

omit [CompleteSpace E] in
@[simp] theorem spectralPlusProj_apply_to_doubled (x y : E) :
    Pplus (to_doubled x y : H2) = plusPoint (E := E) x := by
  apply DoubledSpace.ext <;>
    simp [spectralPlusProj, plusPoint, spectral_epsilon_apply, half_smul_add_half_smul]

omit [CompleteSpace E] in
@[simp] theorem spectralMinusProj_apply_to_doubled (x y : E) :
    Pminus (to_doubled x y : H2) = minusPoint (E := E) y := by
  apply DoubledSpace.ext <;>
    simp [spectralMinusProj, minusPoint, spectral_epsilon_apply, half_smul_add_half_smul]

omit [CompleteSpace E] in
/-- The positive spectral projector is the canonical `plusPoint` extraction. -/
theorem spectralPlusProj_apply_eq_plusPoint (u : H2) :
    Pplus u = plusPoint (E := E) (WithLp.fst u) := by
  have hu : (to_doubled (WithLp.fst u) (WithLp.snd u) : H2) = u := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hu]
  exact spectralPlusProj_apply_to_doubled (E := E) (x := WithLp.fst u) (y := WithLp.snd u)

omit [CompleteSpace E] in
/-- The negative spectral projector is the canonical `minusPoint` extraction. -/
theorem spectralMinusProj_apply_eq_minusPoint (u : H2) :
    Pminus u = minusPoint (E := E) (WithLp.snd u) := by
  have hu : (to_doubled (WithLp.fst u) (WithLp.snd u) : H2) = u := by
    apply DoubledSpace.ext <;> simp [to_doubled]
  rw [← hu]
  exact spectralMinusProj_apply_to_doubled (E := E) (x := WithLp.fst u) (y := WithLp.snd u)

omit [CompleteSpace E] in
/-- The positive spectral projector lands in the `+1` sheet. -/
theorem spectralPlusProj_mem_plusSheet (u : H2) :
    Pplus u ∈ plusSheet (E := E) := by
  rw [spectralPlusProj_apply_eq_plusPoint]
  exact plusPoint_mem_plusSheet (E := E) (WithLp.fst u)

omit [CompleteSpace E] in
/-- The negative spectral projector lands in the `-1` sheet. -/
theorem spectralMinusProj_mem_minusSheet (u : H2) :
    Pminus u ∈ minusSheet (E := E) := by
  rw [spectralMinusProj_apply_eq_minusPoint]
  exact minusPoint_mem_minusSheet (E := E) (WithLp.snd u)

/-- `E` is identified with the positive spectral sheet by `plusPoint`. -/
noncomputable def plusSheetEquiv :
    E ≃ {u : H2 // u ∈ plusSheet (E := E)} where
  toFun x := ⟨plusPoint (E := E) x, plusPoint_mem_plusSheet (E := E) x⟩
  invFun u := WithLp.fst u.1
  left_inv x := by simp
  right_inv u := by
    apply Subtype.ext
    exact (eq_plusPoint_of_mem_plusSheet (E := E) u.2).symm

/-- `E` is identified with the negative spectral sheet by `minusPoint`. -/
noncomputable def minusSheetEquiv :
    E ≃ {u : H2 // u ∈ minusSheet (E := E)} where
  toFun x := ⟨minusPoint (E := E) x, minusPoint_mem_minusSheet (E := E) x⟩
  invFun u := WithLp.snd u.1
  left_inv x := by simp
  right_inv u := by
    apply Subtype.ext
    exact (eq_minusPoint_of_mem_minusSheet (E := E) u.2).symm

/-- Pointwise idempotence of the positive spectral projector. -/
theorem spectralPlusProj_apply_idempotent (u : H2) :
    Pplus (Pplus u) = Pplus u := by
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg (fun F : H2 →L[ℝ] H2 => F u) (spectralPlusProj_idempotent (E := E))

/-- Pointwise idempotence of the negative spectral projector. -/
theorem spectralMinusProj_apply_idempotent (u : H2) :
    Pminus (Pminus u) = Pminus u := by
  simpa [ContinuousLinearMap.comp_apply] using
    congrArg (fun F : H2 →L[ℝ] H2 => F u) (spectralMinusProj_idempotent (E := E))

/-- Pointwise spectral decomposition into positive and negative sectors. -/
theorem spectralProj_decomposition (u : H2) :
    Pplus u + Pminus u = u := by
  simpa [ContinuousLinearMap.add_apply] using (spectral_decomposition (E := E) u).symm

/-- The positive-sector restriction of the split quadratic divergence. -/
noncomputable def polarizedDivergence (q k : H2) : ℝ :=
  SplitQuadratic.divergence (E := E) (Pplus q) (Pplus k)

/-- Restricted nonnegativity on the positive spectral sector. -/
theorem polarizedDivergence_nonneg (q k : H2) :
    0 ≤ polarizedDivergence (E := E) q k := by
  unfold polarizedDivergence
  exact SplitQuadraticSheets.divergence_nonneg_of_mem_plusSheet (E := E)
    (spectralPlusProj_mem_plusSheet (E := E) q)
    (spectralPlusProj_mem_plusSheet (E := E) k)

/-- Restricted nonpositivity on the negative spectral sector. -/
theorem projectedMinus_divergence_nonpos (q k : H2) :
    SplitQuadratic.divergence (E := E) (Pminus q) (Pminus k) ≤ 0 := by
  exact SplitQuadraticSheets.divergence_nonpos_of_mem_minusSheet (E := E)
    (spectralMinusProj_mem_minusSheet (E := E) q)
    (spectralMinusProj_mem_minusSheet (E := E) k)

/-- On the positive spectral sector, the interaction reduces to the Euclidean calibrated form. -/
@[rep_depth krein]
theorem neg_polarizedDivergence_eq_plusSheet_interaction (q k : H2) :
    -polarizedDivergence (E := E) q k
      = inner ℝ (WithLp.fst q) (WithLp.fst k)
          - (1 / 2 : ℝ) * inner ℝ (WithLp.fst q) (WithLp.fst q)
          - (1 / 2 : ℝ) * inner ℝ (WithLp.fst k) (WithLp.fst k) := by
  unfold polarizedDivergence
  rw [spectralPlusProj_apply_eq_plusPoint, spectralPlusProj_apply_eq_plusPoint]
  exact neg_divergence_plusPoint_eq_dot_minus_half_norms (E := E) (WithLp.fst q) (WithLp.fst k)

/-- On the negative spectral sector, the interaction carries the opposite sign. -/
theorem neg_projectedMinusDivergence_eq_minusSheet_interaction (q k : H2) :
    -SplitQuadratic.divergence (E := E) (Pminus q) (Pminus k)
      = -inner ℝ (WithLp.snd q) (WithLp.snd k)
          + (1 / 2 : ℝ) * inner ℝ (WithLp.snd q) (WithLp.snd q)
          + (1 / 2 : ℝ) * inner ℝ (WithLp.snd k) (WithLp.snd k) := by
  rw [spectralMinusProj_apply_eq_minusPoint, spectralMinusProj_apply_eq_minusPoint]
  exact neg_divergence_minusPoint_eq_neg_dot_plus_half_norms (E := E)
    (WithLp.snd q) (WithLp.snd k)

end InfoGeometry.Krein.PolarizedSector
