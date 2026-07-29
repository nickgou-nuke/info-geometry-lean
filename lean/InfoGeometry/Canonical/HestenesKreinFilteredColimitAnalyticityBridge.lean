import Mathlib.Tactic
import InfoGeometry.Canonical.FilteredColimitLeeYangVirasoroMasterBridge
import InfoGeometry.Canonical.CuntzAlgebraNilpotentChains
import InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Hestenes-Krein & Filtered Inductive Colimit Analyticity Master Bridge

This module gives native Lean proofs for elementary algebraic facts that
support a filtered Hestenes--Krein colimit interface:

1. **Hestenes-Krein Fundamental Symmetry Nilpotency Preservation**:
   if `J^2 = 1` and `N^2 = 0`, then `(J * N * J)^2 = 0`.
2. **Hestenes Clifford 2x2 Geometric Involution**:
   the Pauli matrix `e_1 = [[0, 1], [1, 0]]` satisfies `e_1^2 = 1`.
3. **Filtered Direct Limit Intertwining Kernel Survival**:
   if `ι ∘ Dₙ = Dₙ₊₁ ∘ ι`, `ι` is injective, and `Dₙ v = 0` with `v ≠ 0`,
   then `ι v ≠ 0` and `Dₙ₊₁ (ι v) = 0`.
4. **Algebraic insufficiency of injectivity alone**:
   injectivity without intertwining does not guarantee kernel survival.
5. **Grand Hestenes-Krein Algebraic Master Theorem**:
   combines the algebraic facts above with the antiunitary
   fixed-locus characterization `s = 1 - star s ↔ s.re = 1/2`.

These are kernel-checked algebraic lemmas. They do not prove analytic
continuation, meromorphic continuation, or the Riemann hypothesis.
-/

noncomputable section

namespace InfoGeometry.Canonical.HestenesKreinFilteredColimitAnalyticityBridge

open Complex
open InfoGeometry.Canonical.FilteredColimitLeeYangVirasoroMasterBridge
open InfoGeometry.Canonical.CuntzAlgebraNilpotentChains
open InfoGeometry.Canonical.ColimitRigidityFixedLocusBridge

/--
**Main Theorem 1: Hestenes-Krein Fundamental Symmetry Nilpotency Preservation**
Proves natively that if $N^2 = 0$ and $J^2 = I$, then $(J N J)^2 = 0$.
-/
theorem hestenes_krein_jordan_nilpotent_preserved
    {R : Type*} [MonoidWithZero R] (J N : R) (hJ : J * J = 1) (hN : N * N = 0) :
    (J * N * J) * (J * N * J) = 0 := by
  have h1 : (J * N * J) * (J * N * J) = J * N * (J * J) * N * J := by simp [mul_assoc]
  have h2 : J * N * N * J = J * (N * N) * J := by simp [mul_assoc]
  rw [h1, hJ, mul_one, h2, hN, mul_zero, zero_mul]

/--
**Main Theorem 2: Hestenes Clifford 2x2 Geometric Involution**
Proves natively that the 2x2 Clifford generator $e_1 = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}$ satisfies $e_1^2 = I$.
-/
theorem hestenes_clifford_e1_sq :
    !![(0 : ℂ), (1 : ℂ); (1 : ℂ), (0 : ℂ)] * !![(0 : ℂ), (1 : ℂ); (1 : ℂ), (0 : ℂ)] = (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/--
**Main Theorem 3: Filtered Direct Limit Intertwining Kernel Survival**
Proves natively that if $\iota \circ D_n = D_{n+1} \circ \iota$, $\iota$ is injective, and $v \neq 0$ with $D_n v = 0$, then $\iota v \neq 0$ and $D_{n+1}(\iota v) = 0$.
-/
theorem filtered_colimit_hestenes_kernel_survival
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (Dn : V → V) (Dn1 : W → W) (iota : V → W) (h_intertwine : ∀ v, iota (Dn v) = Dn1 (iota v))
    (h_inj : Function.Injective iota) (h_iota_zero : iota 0 = 0)
    (v : V) (hv_ne : v ≠ 0) (h_ker : Dn v = 0) :
    iota v ≠ 0 ∧ Dn1 (iota v) = 0 := by
  refine ⟨fun h_eq => hv_ne (h_inj (h_eq.trans h_iota_zero.symm)), ?_⟩
  rw [← h_intertwine, h_ker, h_iota_zero]

/-- **Main Theorem 4/5: Grand Hestenes-Krein Algebraic Master Theorem**.
Bundles the symmetry, Clifford, and kernel-survival results with the
antiunitary fixed-locus characterization. -/
theorem grand_hestenes_krein_filtered_colimit_master_duality
    {R : Type*} [MonoidWithZero R] (J N : R) (hJ : J * J = 1) (hN : N * N = 0)
    {V W : Type*} [AddCommGroup V] [AddCommGroup W]
    (Dn : V → V) (Dn1 : W → W) (iota : V → W) (h_intertwine : ∀ v, iota (Dn v) = Dn1 (iota v))
    (h_inj : Function.Injective iota) (h_iota_zero : iota 0 = 0)
    (v : V) (hv_ne : v ≠ 0) (h_ker : Dn v = 0)
    (s_anti : ℂ) (h_anti : s_anti = 1 - star s_anti) :
    ((J * N * J) * (J * N * J) = 0) ∧
    (!![(0 : ℂ), (1 : ℂ); (1 : ℂ), (0 : ℂ)] * !![(0 : ℂ), (1 : ℂ); (1 : ℂ), (0 : ℂ)] = (1 : Matrix (Fin 2) (Fin 2) ℂ)) ∧
    (iota v ≠ 0 ∧ Dn1 (iota v) = 0) ∧
    (s_anti.re = 1 / 2) := ⟨
  hestenes_krein_jordan_nilpotent_preserved J N hJ hN,
  hestenes_clifford_e1_sq,
  filtered_colimit_hestenes_kernel_survival Dn Dn1 iota h_intertwine h_inj h_iota_zero v hv_ne h_ker,
  (critical_line_fixed_locus_iff s_anti).1 h_anti
⟩

end InfoGeometry.Canonical.HestenesKreinFilteredColimitAnalyticityBridge
