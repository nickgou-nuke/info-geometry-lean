import Mathlib.Tactic

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Hestenes--Krein finite algebraic readouts

This module gives native Lean proofs for three elementary algebraic facts:

1. Conjugation by an involution preserves square-zero elements.
2. A concrete two-by-two involution squares to the identity.
3. An injective intertwiner transports a nonzero kernel vector to the next
   stage and preserves the kernel equation.

No colimit, analytic-continuation, or spectral theorem is defined here.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinFilteredColimitAnalyticityBridge


/--
**Conjugated square-zero element.**
If `J² = 1` and `N² = 0`, then `(J * N * J)² = 0`.
-/
theorem hestenes_krein_jordan_nilpotent_preserved
    {R : Type*} [MonoidWithZero R] (J N : R) (hJ : J * J = 1) (hN : N * N = 0) :
    (J * N * J) * (J * N * J) = 0 := by
  have h1 : (J * N * J) * (J * N * J) = J * N * (J * J) * N * J := by simp [mul_assoc]
  have h2 : J * N * N * J = J * (N * N) * J := by simp [mul_assoc]
  rw [h1, hJ, mul_one, h2, hN, mul_zero, zero_mul]

/--
**Concrete matrix involution.**
The displayed two-by-two matrix squares to the identity.
-/
theorem hestenes_clifford_e1_sq :
    !![(0 : ℂ), (1 : ℂ); (1 : ℂ), (0 : ℂ)] * !![(0 : ℂ), (1 : ℂ); (1 : ℂ), (0 : ℂ)] = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
**Finite intertwining kernel transport.**
An injective intertwiner sends a nonzero kernel vector to a nonzero vector in
the target kernel.
-/
theorem filtered_colimit_hestenes_kernel_survival
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (Dn : V → V) (Dn1 : W → W) (iota : V → W) (h_intertwine : ∀ v, iota (Dn v) = Dn1 (iota v))
    (h_inj : Function.Injective iota) (h_iota_zero : iota 0 = 0)
    (v : V) (hv_ne : v ≠ 0) (h_ker : Dn v = 0) :
    iota v ≠ 0 ∧ Dn1 (iota v) = 0 := by
  refine ⟨fun h_eq => hv_ne (h_inj (h_eq.trans h_iota_zero.symm)), ?_⟩
  rw [← h_intertwine, h_ker, h_iota_zero]

end InfoGeometry.Canonical.HestenesKreinFilteredColimitAnalyticityBridge
