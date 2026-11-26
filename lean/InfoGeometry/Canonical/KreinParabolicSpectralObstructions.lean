/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import InfoGeometry.Core.PeirceDecomposition

/-!
# Exact 2×2 Krein, Oblique-Projector, and Parabolic-Coalescence Obstruction Witnesses

Finite-dimensional counterexamples illustrating three structural obstructions
relevant to indefinite-signature spectral/trace arguments:

1. **Indefinite Krein/Peirce polarity (`diag(1, -1)`)**: involutive (`Γ² = 1`)
   with vanishing algebraic trace (`Tr(Γ) = 0`), yet positive diagonal `ℓ¹` norm `2`.
2. **Oblique idempotent / Markushevich dual blow-up (`Ω_θ`)**: for the unit-norm
   tilted basis `e₁ = (1, 0)`, `e₂ = (cos θ, sin θ)` (`sin θ ≠ 0`),
   `Ω_θ = !![1, -cos θ / sin θ; 0, 0]` is idempotent, fixes `e₁`, and annihilates `e₂`,
   while its off-diagonal entry `-cos θ / sin θ` diverges as `θ → 0`.
3. **Parabolic coalescence / Jordan block limit**: for `λ₁ ≠ λ₂`,
   `P₁ = !![1, (λ₁ - λ₂)⁻¹; 0, 0]` is the unique left eigenprojector of
   `!![λ₁, 1; 0, λ₂]` (diverging as `λ₁ → λ₂`), whereas at coalescence `λ₁ = λ₂`
   the nilpotent shift `N = !![0, 1; 0, 0]` is nonzero with `N² = 0`.
-/

noncomputable section

namespace InfoGeometry.Canonical.KreinParabolicSpectralObstructions

open scoped Matrix

/-- Krein/Peirce polarity involution `diag(1, -1)` on `ℝ²`. -/
def kreinPolarity2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, -1]

/-- `diag(1, -1)` is an involution with vanishing algebraic trace `0`, yet positive
sum of absolute diagonal entries `2`.  This is not a claim about a nuclear norm. -/
theorem kreinPolarity2_obstruction :
    kreinPolarity2 * kreinPolarity2 = 1 ∧
      Matrix.trace kreinPolarity2 = 0 ∧
      (∑ i : Fin 2, |kreinPolarity2 i i|) = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [kreinPolarity2, Matrix.mul_apply, Fin.sum_univ_two]
  · norm_num [kreinPolarity2, Matrix.trace, Fin.sum_univ_two]
  · norm_num [kreinPolarity2, Fin.sum_univ_two]

/-- A diagonal signature matrix with entries squaring to one has absolute
diagonal mass equal to its dimension, even when its algebraic trace cancels.
This is the arbitrary-finite-dimensional version of the `diag(1, -1)` witness;
the absolute diagonal sum is stated explicitly and is not called a trace norm. -/
theorem diagonalSignature_trace_cancellation_and_abs_mass
    {n : ℕ} (ε : Fin n → ℝ)
    (hε : ∀ i, ε i ^ 2 = 1)
    (htrace : Matrix.trace (Matrix.diagonal ε) = 0) :
    Matrix.trace (Matrix.diagonal ε) = 0 ∧
      (∑ i : Fin n, |(Matrix.diagonal ε) i i|) = (Fintype.card (Fin n) : ℝ) := by
  refine ⟨htrace, ?_⟩
  have hunit (i : Fin n) : |ε i| = 1 := by
    rcases sq_eq_one_iff.mp (hε i) with h | h
    · simp [h]
    · simp [h]
  calc
    (∑ i : Fin n, |(Matrix.diagonal ε) i i|) = ∑ i : Fin n, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hunit i]
    _ = (Fintype.card (Fin n) : ℝ) := by simp

/-- Oblique idempotent `Ω_θ = !![1, -cos θ / sin θ; 0, 0]` for the unit-norm tilted
basis `e₁ = (1, 0)`, `e₂ = (cos θ, sin θ)`. -/
def obliqueProjector (θ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, -(Real.cos θ / Real.sin θ); 0, 0]

/-- `Ω_θ` is idempotent, fixes `e₁ = (1, 0)`, and annihilates `e₂ = (cos θ, sin θ)`
whenever `sin θ ≠ 0`. -/
theorem obliqueProjector_properties (θ : ℝ) (hsin : Real.sin θ ≠ 0) :
    obliqueProjector θ * obliqueProjector θ = obliqueProjector θ ∧
      obliqueProjector θ *ᵥ ![1, 0] = ![1, 0] ∧
      obliqueProjector θ *ᵥ ![Real.cos θ, Real.sin θ] = 0 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [obliqueProjector, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i
    fin_cases i <;>
      simp [obliqueProjector, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · ext i
    fin_cases i <;>
      simp [obliqueProjector, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        div_mul_cancel₀ _ hsin]

/-- Quantitative conditioning bound for the oblique projector.  If the tilted
vectors have transverse separation at most `δ`, while their longitudinal
overlap is at least `c`, the off-diagonal coordinate of the projection is at
least `c / δ`.  Thus any uniform bound on this family requires a uniform
lower bound on the angle (or a compensating decay of the overlap). -/
theorem obliqueProjector_shear_lower_bound
    (θ c δ : ℝ) (hc : 0 < c) (hδ : 0 < δ)
    (hsin : 0 < Real.sin θ) (hsinδ : Real.sin θ ≤ δ)
    (hcos : c ≤ |Real.cos θ|) :
    0 < c / δ ∧ c / δ ≤ |Real.cos θ / Real.sin θ| := by
  refine ⟨div_pos hc hδ, ?_⟩
  rw [abs_div, abs_of_pos hsin]
  apply (div_le_div_iff₀ hδ hsin).2
  calc
    c * Real.sin θ ≤ |Real.cos θ| * Real.sin θ :=
      mul_le_mul_of_nonneg_right hcos (le_of_lt hsin)
    _ ≤ |Real.cos θ| * δ :=
      mul_le_mul_of_nonneg_left hsinδ (abs_nonneg _)

/-- Spectral projector `P₁ = !![1, (λ₁ - λ₂)⁻¹; 0, 0]` for `!![λ₁, 1; 0, λ₂]`
with distinct eigenvalues `λ₁ ≠ λ₂`. -/
def coalescingSpectralProjector (lam₁ lam₂ : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1, (lam₁ - lam₂)⁻¹; 0, 0]

/-- For `λ₁ ≠ λ₂`, `P₁` is an idempotent left eigenprojector of `!![λ₁, 1; 0, λ₂]`
whose off-diagonal entry `(λ₁ - λ₂)⁻¹` diverges as `λ₁ → λ₂`, while at coalescence
`λ₁ = λ₂` the nilpotent shift `N = !![0, 1; 0, 0]` is nonzero with `N² = 0`. -/
theorem parabolic_coalescence_obstruction (lam₁ lam₂ : ℝ) (hne : lam₁ ≠ lam₂) :
    coalescingSpectralProjector lam₁ lam₂ * coalescingSpectralProjector lam₁ lam₂ =
        coalescingSpectralProjector lam₁ lam₂ ∧
      coalescingSpectralProjector lam₁ lam₂ *
          (!![lam₁, (1 : ℝ); 0, lam₂] : Matrix (Fin 2) (Fin 2) ℝ) =
        lam₁ • coalescingSpectralProjector lam₁ lam₂ ∧
      (!![(0 : ℝ), 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) ≠ 0 ∧
      (!![(0 : ℝ), 1; 0, 0] : Matrix (Fin 2) (Fin 2) ℝ) * !![0, 1; 0, 0] = 0 := by
  have hsub : lam₁ - lam₂ ≠ 0 := sub_ne_zero.mpr hne
  refine ⟨?_, ?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coalescingSpectralProjector, Matrix.mul_apply, Fin.sum_univ_two]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [coalescingSpectralProjector, Matrix.mul_apply, Fin.sum_univ_two]
    calc
      1 + (lam₁ - lam₂)⁻¹ * lam₂
          = (lam₁ - lam₂) * (lam₁ - lam₂)⁻¹ + lam₂ * (lam₁ - lam₂)⁻¹ := by
            rw [mul_inv_cancel₀ hsub, mul_comm]
      _ = ((lam₁ - lam₂) + lam₂) * (lam₁ - lam₂)⁻¹ := (add_mul _ _ _).symm
      _ = lam₁ * (lam₁ - lam₂)⁻¹ := by rw [sub_add_cancel]
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    norm_num at h01
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Matrix.mul_apply, Fin.sum_univ_two]

/-- A small nonzero spectral separation forces the off-diagonal entry of the
two-eigenvalue spectral projector to be large.  This is a quantitative
condition bound; it does not assert convergence of projectors at collision. -/
theorem coalescingSpectralProjector_shear_lower_bound
    (lam₁ lam₂ δ : ℝ) (hgap : lam₁ ≠ lam₂)
    (hδ : 0 < δ) (hsmall : |lam₁ - lam₂| ≤ δ) :
    1 / δ ≤ |(lam₁ - lam₂)⁻¹| := by
  have hgapAbs : 0 < |lam₁ - lam₂| := abs_pos.mpr (sub_ne_zero.mpr hgap)
  have hbound : 1 / δ ≤ 1 / |lam₁ - lam₂| :=
    (div_le_div_iff₀ hδ hgapAbs).2 (by simpa using hsmall)
  calc
    1 / δ ≤ 1 / |lam₁ - lam₂| := hbound
    _ = |(lam₁ - lam₂)⁻¹| := by rw [abs_inv]; simp

/-- Peirce cut projector `P₀ = diag(1, 0)` in `Matrix (Fin 2) (Fin 2) ℝ`. -/
def peirceCut2 : Matrix (Fin 2) (Fin 2) ℝ := !![1, 0; 0, 0]

/-- Strictly lower-triangular parabolic nilpotent `X = !![0, 0; 1, 0]`. -/
def nilpotentLower2 : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]

/-- `ERRATA F9` witness: Peirce cut `P₀ = diag(1, 0)` and parabolic nilpotent
`X = !![0, 0; 1, 0]` satisfy `P₀ * X = 0` yet `X * P₀ = X ≠ 0`, proving
strict non-commutativity `P₀ * X ≠ X * P₀` (hence `‖P₀ X‖₁ = 0 ≠ 1 = ‖X P₀‖₁`). -/
theorem peirceCut_nilpotent_noncommute :
    peirceCut2 * nilpotentLower2 = 0 ∧
      nilpotentLower2 * peirceCut2 = nilpotentLower2 ∧
      peirceCut2 * nilpotentLower2 ≠ nilpotentLower2 * peirceCut2 := by
  have hPX : peirceCut2 * nilpotentLower2 = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [peirceCut2, nilpotentLower2, Matrix.mul_apply, Fin.sum_univ_two]
  have hXP : nilpotentLower2 * peirceCut2 = nilpotentLower2 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [peirceCut2, nilpotentLower2, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨hPX, hXP, ?_⟩
  intro h
  rw [hPX, hXP] at h
  have h10 := congrFun (congrFun h 1) 0
  norm_num [nilpotentLower2] at h10

/-- Explicit standalone non-commutativity witness in `Matrix (Fin 2) (Fin 2) ℝ`. -/
theorem peirceCut2_noncommute :
    peirceCut2 * nilpotentLower2 ≠ nilpotentLower2 * peirceCut2 :=
  peirceCut_nilpotent_noncommute.2.2

/-- The noncommuting cut witness occupies only one directed Peirce corner.
Thus idempotence of the cut and noncommutation alone do not force a reciprocal
pair of nonzero off-diagonal channels. -/
theorem peirceCut_nilpotent_one_sided_corner :
    InfoGeometry.Core.PeirceDecomposition.component10 peirceCut2 nilpotentLower2 = 0 ∧
    InfoGeometry.Core.PeirceDecomposition.component01 peirceCut2 nilpotentLower2 =
      nilpotentLower2 := by
  constructor <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    norm_num [InfoGeometry.Core.PeirceDecomposition.component10,
      InfoGeometry.Core.PeirceDecomposition.component01,
      InfoGeometry.Core.PeirceDecomposition.complementIdempotent,
      peirceCut2, nilpotentLower2, Matrix.mul_apply, Fin.sum_univ_two]

/-- A noncommuting idempotent cut can have only one nonzero Peirce arrow.
This concrete `2 × 2` witness rules out deriving reciprocal coupling from
idempotence and noncommutation alone. -/
theorem peirceCut_nilpotent_one_sided_counterexample :
    peirceCut2 * peirceCut2 = peirceCut2 ∧
    peirceCut2 * nilpotentLower2 ≠ nilpotentLower2 * peirceCut2 ∧
    InfoGeometry.Core.PeirceDecomposition.component10 peirceCut2 nilpotentLower2 = 0 ∧
    InfoGeometry.Core.PeirceDecomposition.component01 peirceCut2 nilpotentLower2 =
      nilpotentLower2 := by
  refine ⟨?_, peirceCut2_noncommute, peirceCut_nilpotent_one_sided_corner⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [peirceCut2, Matrix.mul_apply, Fin.sum_univ_two]

end InfoGeometry.Canonical.KreinParabolicSpectralObstructions
