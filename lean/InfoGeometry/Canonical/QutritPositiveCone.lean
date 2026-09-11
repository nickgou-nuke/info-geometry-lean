import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Quantum.QutritDensityMatrix
import InfoGeometry.Quantum.QutritGates

/-!
# The finite complex qutrit positive cone

`Matrix.PosSemidef` in Mathlib is formulated for ordered star-rings.  There is
no ordered-ring structure on `ℂ`, so the complex qutrit cone is expressed by
its native Hermitian quadratic-form predicate: the real part of every finite
quadratic form is nonnegative.  This is a predicate on the concrete matrices,
not a supplied witness or an abstract positivity wrapper.
-/

noncomputable section

open Matrix
open scoped ComplexConjugate

namespace InfoGeometry.Quantum.Qutrit

/-- Complex Hermitian positive semidefiniteness for a finite qutrit matrix. -/
def QutritPosSemidef (ρ : QutritMatrix) : Prop :=
  ρ.IsHermitian ∧
    ∀ x : Fin 3 → ℂ, 0 ≤ Complex.re (star x ⬝ᵥ (ρ *ᵥ x))

/-- The trace-one section of the finite qutrit positive cone. -/
def QutritDensity (ρ : QutritMatrix) : Prop :=
  QutritPosSemidef ρ ∧ Matrix.trace ρ = 1

theorem qutritPosSemidef_add {ρ σ : QutritMatrix}
    (hρ : QutritPosSemidef ρ) (hσ : QutritPosSemidef σ) :
    QutritPosSemidef (ρ + σ) := by
  refine ⟨hρ.1.add hσ.1, fun x => ?_⟩
  rw [add_mulVec, dotProduct_add]
  exact add_nonneg (hρ.2 x) (hσ.2 x)

theorem qutritPosSemidef_nonneg_smul {r : ℝ} {ρ : QutritMatrix}
    (hr : 0 ≤ r) (hρ : QutritPosSemidef ρ) :
    QutritPosSemidef (r • ρ) := by
  refine ⟨by
      change ((r : ℂ) • ρ)ᴴ = (r : ℂ) • ρ
      rw [conjTranspose_smul, hρ.1]
      simp, fun x => ?_⟩
  rw [smul_mulVec, dotProduct_smul, Complex.smul_re]
  change 0 ≤ r * Complex.re (star x ⬝ᵥ (ρ *ᵥ x))
  exact mul_nonneg hr (hρ.2 x)

private lemma pure_quadratic_eq_normSq (ψ : QutritState) (x : Fin 3 → ℂ) :
    Complex.re (star x ⬝ᵥ (pureDensityMatrix ψ *ᵥ x)) =
      Complex.normSq (star (ψ : QutritSpace) ⬝ᵥ x) := by
  simp [pureDensityMatrix, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, Complex.normSq_apply]
  ring_nf

theorem pureDensityMatrix_posSemidef (ψ : QutritState) :
    QutritPosSemidef (pureDensityMatrix ψ) := by
  refine ⟨?_, fun x => ?_⟩
  · change (pureDensityMatrix ψ)ᴴ = pureDensityMatrix ψ
    exact pureDensityMatrix_star ψ
  · rw [pure_quadratic_eq_normSq]
    exact Complex.normSq_nonneg _

theorem pureDensityMatrix_qutritDensity (ψ : QutritState) :
    QutritDensity (pureDensityMatrix ψ) :=
  ⟨pureDensityMatrix_posSemidef ψ, pureDensityMatrix_trace ψ⟩

theorem qutritDensity_trace_one {ρ : QutritMatrix}
    (hρ : QutritDensity ρ) : Matrix.trace ρ = 1 :=
  hρ.2

theorem qutritPosSemidef_diagonal_re_nonneg {ρ : QutritMatrix}
    (hρ : QutritPosSemidef ρ) (i : Fin 3) :
    0 ≤ Complex.re (ρ i i) := by
  have h := hρ.2 (Pi.single i 1)
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using h

theorem qutritPosSemidef_trace_re_nonneg {ρ : QutritMatrix}
    (hρ : QutritPosSemidef ρ) :
    0 ≤ Complex.re (Matrix.trace ρ) := by
  have hsum : 0 ≤ (ρ 0 0).re + (ρ 1 1).re + (ρ 2 2).re :=
    add_nonneg
      (add_nonneg
        (qutritPosSemidef_diagonal_re_nonneg hρ 0)
        (qutritPosSemidef_diagonal_re_nonneg hρ 1))
      (qutritPosSemidef_diagonal_re_nonneg hρ 2)
  simpa [Matrix.trace, Fin.sum_univ_succ, Complex.add_re, add_assoc] using hsum

theorem qutritDensity_convex {r s : ℝ} {ρ σ : QutritMatrix}
    (hr : 0 ≤ r) (hs : 0 ≤ s) (hrs : r + s = 1)
    (hρ : QutritDensity ρ) (hσ : QutritDensity σ) :
    QutritDensity (r • ρ + s • σ) := by
  refine ⟨qutritPosSemidef_add
      (qutritPosSemidef_nonneg_smul hr hρ.1)
      (qutritPosSemidef_nonneg_smul hs hσ.1), ?_⟩
  rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul, hρ.2, hσ.2]
  norm_num
  exact_mod_cast hrs

theorem qutritIdentity_posSemidef :
    QutritPosSemidef (1 : QutritMatrix) := by
  refine ⟨by simp, fun x => ?_⟩
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  nlinarith [sq_nonneg (x 0).re, sq_nonneg (x 0).im,
    sq_nonneg (x 1).re, sq_nonneg (x 1).im,
    sq_nonneg (x 2).re, sq_nonneg (x 2).im]

def maximallyMixedQutrit : QutritMatrix :=
  (1 / 3 : ℝ) • (1 : QutritMatrix)

theorem maximallyMixedQutrit_posSemidef :
    QutritPosSemidef maximallyMixedQutrit := by
  exact qutritPosSemidef_nonneg_smul (by norm_num)
    qutritIdentity_posSemidef

theorem maximallyMixedQutrit_density :
    QutritDensity maximallyMixedQutrit := by
  refine ⟨maximallyMixedQutrit_posSemidef, ?_⟩
  simp [maximallyMixedQutrit, Matrix.trace]

end InfoGeometry.Quantum.Qutrit
