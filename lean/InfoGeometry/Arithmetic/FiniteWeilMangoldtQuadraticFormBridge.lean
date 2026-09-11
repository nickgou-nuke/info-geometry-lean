import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.FiniteMangoldtDirichletConvolutionBridge

/-!
# Finite Weil--Mangoldt quadratic-form shadow

This owner formalizes only the finite prime/Mangoldt contribution built from a
supplied family of self-adjoint operators.  The operators are an explicit
interface: no Connes--Consani--Moscovici realization, unbounded generator,
functional calculus, determinant, spectral convergence, or RH statement is
asserted.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.FiniteWeilMangoldtQuadraticFormBridge

open scoped BigOperators InnerProductSpace

/-- A finite-dimensional or infinite Hilbert carrier with a self-adjoint
operator family. -/
structure FiniteWeilOperatorDatum (H : Type*)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  T : ℕ → H →ₗ[ℂ] H
  selfAdjoint_T : ∀ n f g,
    ⟪f, T n g⟫_ℂ = ⟪T n f, g⟫_ℂ

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- The finite prime/Mangoldt contribution with cutoff `X`. -/
def finiteWeilPrimeQuadraticForm
    (D : FiniteWeilOperatorDatum H) (X : ℕ) (f g : H) : ℂ :=
  -∑ n ∈ Finset.Icc 2 X,
      (ArithmeticFunction.vonMangoldt n : ℂ) * ⟪f, D.T n g⟫_ℂ

theorem finiteWeilPrimeQuadraticForm_hermitian
    (D : FiniteWeilOperatorDatum H) (X : ℕ) (f g : H) :
    finiteWeilPrimeQuadraticForm D X g f =
      star (finiteWeilPrimeQuadraticForm D X f g) := by
  unfold finiteWeilPrimeQuadraticForm
  change -∑ n ∈ Finset.Icc 2 X,
      (ArithmeticFunction.vonMangoldt n : ℂ) * ⟪g, D.T n f⟫_ℂ =
    (starRingEnd ℂ) (-∑ n ∈ Finset.Icc 2 X,
      (ArithmeticFunction.vonMangoldt n : ℂ) * ⟪f, D.T n g⟫_ℂ)
  simp only [map_neg, map_sum, map_mul, starRingEnd_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hinner : star (⟪f, D.T n g⟫_ℂ) = ⟪g, D.T n f⟫_ℂ := by
    change (starRingEnd ℂ) (⟪f, D.T n g⟫_ℂ) = _
    rw [inner_conj_symm]
    exact (D.selfAdjoint_T n g f).symm
  rw [hinner]
  simp

theorem finiteWeilPrimeQuadraticForm_diagonal_is_real
    (D : FiniteWeilOperatorDatum H) (X : ℕ) (f : H) :
    ∃ r : ℝ, finiteWeilPrimeQuadraticForm D X f f = r := by
  refine ⟨(finiteWeilPrimeQuadraticForm D X f f).re, ?_⟩
  have hreal :
      star (finiteWeilPrimeQuadraticForm D X f f) =
        finiteWeilPrimeQuadraticForm D X f f := by
    symm
    exact finiteWeilPrimeQuadraticForm_hermitian D X f f
  exact (Complex.conj_eq_iff_re.mp hreal).symm

end InfoGeometry.Arithmetic.FiniteWeilMangoldtQuadraticFormBridge
