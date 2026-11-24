/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.Synthesis.ShirokovRecursiveInverse
import InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

/-!
# Fierz aggregate Shirokov coefficient collapse

This owner connects the existing Fierz solder rank-one operator with the
representation-independent Shirokov recurrence.  It works on the real
split-spinor carrier already present in the repository; it does not assert a
complex `Cl(1,3) ≃ End(ℂ⁴)` Dirac-adjoint theorem.

For a rank-one Fierz aggregate `a = ψ χ̄` with `a² = s a`, the Shirokov
readout gives `C₁ = s` and `U₂ = U₃ = U₄ = 0`, hence `C₂ = C₃ = C₄ = 0`.
When `s = 0` the aggregate may be nonzero and nilpotent, so these
characteristic coefficients do not recover the full Fierz bilinear data.
-/

noncomputable section

namespace InfoGeometry.Synthesis.FierzShirokovCoefficientBridge

open InfoGeometry.Synthesis.ShirokovRecursiveInverse
open InfoGeometry.CliffordWeyl.SpinorBilinearSoldering

variable {R A : Type*} [Field R] [Ring A] [Algebra R A]

/-- The first Shirokov coefficient is recovered from the normalized rank-zero readout. -/
theorem shirokovC_one_of_readout (φ : A →ₗ[R] R) (N : ℕ) (hN : (N : R) ≠ 0)
    (a : A) (s : R) (hφa : φ a = s / (N : R)) :
    shirokovC φ N a 0 = s := by
  rw [shirokovC_zero, hφa]
  field_simp [hN]

/-- For a rank-one aggregate `a² = s a`, the second Shirokov multivector vanishes. -/
theorem shirokovU_one_eq_zero (φ : A →ₗ[R] R) (N : ℕ) (hN : (N : R) ≠ 0)
    (a : A) (s : R) (hφa : φ a = s / (N : R))
    (ha2 : a * a = algebraMap R A s * a) :
    shirokovU φ N a 1 = 0 := by
  rw [shirokovU_succ, shirokovU_zero, shirokovC_one_of_readout φ N hN a s hφa,
    mul_sub, ha2, Algebra.commutes]
  simp

/-- A vanishing Shirokov multivector `U_{k+1}` forces the next coefficient to vanish. -/
theorem shirokovC_eq_zero_of_u_succ_eq_zero (φ : A →ₗ[R] R) (N : ℕ) (a : A) (k : ℕ)
    (hU : shirokovU φ N a (k + 1) = 0) : shirokovC φ N a (k + 1) = 0 := by
  rw [shirokovC_succ, ← shirokovU_succ, hU]
  simp

/-- After the rank-one collapse, every later multivector vanishes. -/
theorem shirokovU_eq_zero_of_one_le (φ : A →ₗ[R] R) (N : ℕ) (hN : (N : R) ≠ 0)
    (a : A) (s : R) (hφa : φ a = s / (N : R))
    (ha2 : a * a = algebraMap R A s * a) :
    ∀ k : ℕ, 1 ≤ k → shirokovU φ N a k = 0 := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
      cases k with
      | zero => exact shirokovU_one_eq_zero φ N hN a s hφa ha2
      | succ k =>
          have hprev : shirokovU φ N a (k + 1) = 0 := ih (by omega)
          rw [shirokovU_succ, hprev, shirokovC_eq_zero_of_u_succ_eq_zero φ N a k hprev]
          simp

/-- A rank-one collapse makes every Shirokov coefficient after the first
vanish, uniformly at all finite recurrence indices. -/
theorem shirokovC_eq_zero_of_one_le (φ : A →ₗ[R] R) (N : ℕ) (hN : (N : R) ≠ 0)
    (a : A) (s : R) (hφa : φ a = s / (N : R))
    (ha2 : a * a = algebraMap R A s * a) :
    ∀ k : ℕ, 1 ≤ k → shirokovC φ N a k = 0 := by
  intro k hk
  cases k with
  | zero => omega
  | succ j =>
      have hU : shirokovU φ N a (j + 1) = 0 :=
        shirokovU_eq_zero_of_one_le φ N hN a s hφa ha2 (j + 1) (by omega)
      exact shirokovC_eq_zero_of_u_succ_eq_zero φ N a j hU

/-- A normalized-trace-one idempotent is the projector specialization of the
rank-one collapse: its first coefficient is one and all later coefficients vanish. -/
theorem shirokovC_collapse_of_idempotent_rank_one (φ : A →ₗ[R] R) (N : ℕ)
    (hN : (N : R) ≠ 0) (p : A) (hp : p * p = p)
    (hφp : φ p = (N : R)⁻¹) :
    shirokovC φ N p 0 = 1 ∧ ∀ k : ℕ, 1 ≤ k → shirokovC φ N p k = 0 := by
  have hφp' : φ p = (1 : R) / (N : R) := by
    simpa [div_eq_mul_inv] using hφp
  have hp1 : p * p = algebraMap R A 1 * p := by
    rw [hp]
    simp
  exact ⟨shirokovC_one_of_readout φ N hN p 1 hφp',
    shirokovC_eq_zero_of_one_le φ N hN p 1 hφp' hp1⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The normalized trace used as Shirokov's rank-zero readout on square matrices. -/
def normalizedTrace (N : ℕ) : Matrix ι ι ℝ →ₗ[ℝ] ℝ :=
  (N : ℝ)⁻¹ • (Matrix.traceLinearMap ι ℝ ℝ)

/-- A Fierz solder operator has normalized trace equal to its bilinear scalar divided by `N`. -/
theorem normalizedTrace_solder (N : ℕ) (metric : Matrix ι ι ℝ) (left right : ι → ℝ) :
    normalizedTrace (ι := ι) N (solder metric left right) =
      (diracRow metric right ⬝ᵥ left) / (N : ℝ) := by
  have htr : Matrix.trace (solder metric left right) =
      diracRow metric right ⬝ᵥ left := by
    simpa [bilinear] using
      (solder_trace_readout metric (1 : Matrix ι ι ℝ) left right)
  simp [normalizedTrace, htr, div_eq_mul_inv, mul_comm]

/-- The rank-one Fierz aggregate has `a² = s a` by the existing solder product law. -/
theorem solder_sq_eq_scalar_mul (metric : Matrix ι ι ℝ) (left right : ι → ℝ) :
    solder metric left right * solder metric left right =
      algebraMap ℝ (Matrix ι ι ℝ) (diracRow metric right ⬝ᵥ left) *
        solder metric left right := by
  simpa [Algebra.smul_def] using
    (solder_fierz_product metric left right left right)

/-- Main bridge: Shirokov invariants collapse for a rank-one Fierz aggregate. -/
theorem solder_shirokov_coefficient_collapse (N : ℕ) (hN : (N : ℝ) ≠ 0)
    (metric : Matrix ι ι ℝ) (left right : ι → ℝ) :
    let φ := normalizedTrace (ι := ι) N
    let a := solder metric left right
    let s := diracRow metric right ⬝ᵥ left
    shirokovC φ N a 0 = s ∧
    shirokovC φ N a 1 = 0 ∧
    shirokovC φ N a 2 = 0 ∧
    shirokovC φ N a 3 = 0 := by
  let φ := normalizedTrace (ι := ι) N
  let a := solder metric left right
  let s := diracRow metric right ⬝ᵥ left
  have hφa : φ a = s / (N : ℝ) := by
    simpa [φ, a, s] using normalizedTrace_solder (ι := ι) N metric left right
  have ha2 : a * a = algebraMap ℝ (Matrix ι ι ℝ) s * a := by
    simpa [a, s] using solder_sq_eq_scalar_mul metric left right
  have hU := shirokovU_eq_zero_of_one_le φ N hN a s hφa ha2
  refine ⟨shirokovC_one_of_readout φ N hN a s hφa, ?_, ?_, ?_⟩
  · exact shirokovC_eq_zero_of_u_succ_eq_zero φ N a 0 (hU 1 (by omega))
  · exact shirokovC_eq_zero_of_u_succ_eq_zero φ N a 1 (hU 2 (by omega))
  · exact shirokovC_eq_zero_of_u_succ_eq_zero φ N a 2 (hU 3 (by omega))

/-- Nilpotent limit: a nonzero aggregate with vanishing bilinear scalar is square-zero,
but all its Shirokov characteristic coefficients still vanish. -/
theorem solder_shirokov_nilpotent_limit (N : ℕ) (hN : (N : ℝ) ≠ 0)
    (metric : Matrix ι ι ℝ) (left right : ι → ℝ)
    (hzero : diracRow metric right ⬝ᵥ left = 0)
    (hnonzero : solder metric left right ≠ 0) :
    let a := solder metric left right
    a * a = 0 ∧ a ≠ 0 ∧
    shirokovC (normalizedTrace (ι := ι) N) N a 0 = 0 ∧
    shirokovC (normalizedTrace (ι := ι) N) N a 1 = 0 ∧
    shirokovC (normalizedTrace (ι := ι) N) N a 2 = 0 ∧
    shirokovC (normalizedTrace (ι := ι) N) N a 3 = 0 := by
  let a := solder metric left right
  have hnil : a * a = 0 := by
    simpa [a, hzero] using solder_fierz_product metric left right left right
  have hcoeff := solder_shirokov_coefficient_collapse (ι := ι) N hN metric left right
  dsimp only at hcoeff
  refine ⟨hnil, by simpa [a] using hnonzero, ?_, hcoeff.2.1, hcoeff.2.2.1, hcoeff.2.2.2⟩
  simpa [hzero] using hcoeff.1

end InfoGeometry.Synthesis.FierzShirokovCoefficientBridge
