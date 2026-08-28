import Mathlib
import InfoGeometry.Prequantum.JaynesKLPotential

open scoped BigOperators

namespace InfoGeometry.Thermodynamics.FiniteKLNonnegativity

variable {I : Type*} [Fintype I]

noncomputable def finiteKL (p q : I → ℝ) : ℝ :=
  ∑ i : I, p i * Real.log (p i / q i)

theorem finiteKL_nonneg
    (p q : I → ℝ)
    (hp_sum : ∑ i : I, p i = 1)
    (hq_sum : ∑ i : I, q i = 1)
    (hp_pos : ∀ i : I, 0 < p i)
    (hq_pos : ∀ i : I, 0 < q i) :
    0 ≤ finiteKL p q := by
  have hterm : ∀ i : I,
      0 ≤ InfoGeometry.Prequantum.JaynesKLPotential.scalarKLDivergence (p i) (q i) := by
    intro i
    exact InfoGeometry.Prequantum.JaynesKLPotential.scalarKLDivergence_nonneg
      (p i) (q i) (hp_pos i) (hq_pos i)
  have hsum : 0 ≤ ∑ i : I,
      InfoGeometry.Prequantum.JaynesKLPotential.scalarKLDivergence (p i) (q i) :=
    Finset.sum_nonneg fun i _ => hterm i
  calc
    0 ≤ ∑ i : I,
        InfoGeometry.Prequantum.JaynesKLPotential.scalarKLDivergence (p i) (q i) := hsum
    _ = finiteKL p q := by
      unfold InfoGeometry.Prequantum.JaynesKLPotential.scalarKLDivergence finiteKL
      simp_rw [sub_eq_add_neg]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      rw [hp_sum, hq_sum]
      ring

@[simp] theorem finiteKL_self_zero
    (p : I → ℝ) (hp_pos : ∀ i : I, 0 < p i) :
    finiteKL p p = 0 := by
  unfold finiteKL
  apply Finset.sum_eq_zero
  intro i hi
  rw [div_self (ne_of_gt (hp_pos i)), Real.log_one, mul_zero]

end InfoGeometry.Thermodynamics.FiniteKLNonnegativity
