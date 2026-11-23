/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Trace
import InfoGeometry.Canonical.SouriauMetriplecticAttentionCasimirPoset

/-!
# Matrix instance of the Souriau metriplectic attention theorems

Instantiates the abstract ring results of
`InfoGeometry.Canonical.SouriauMetriplecticAttentionCasimirPoset` at square matrices
`Matrix n n R` with the cyclic functional `τ = Matrix.trace`:

* `trace_cyclic` – the trace satisfies the cyclicity hypothesis `h_cyc`.
* `matrix_spectral_moments_conserved` – Theorem 2 (moment conservation under the
  Brockett–Souriau flow) for matrices.
* `matrix_barrier_potential_nonneg_and_faithful` – Theorem 4 for Hermitian matrices over a
  star-ordered ring without zero divisors (e.g. `ℝ`): `0 ≤ tr V` and `tr V = 0 ↔ [P, X] = 0`.
* `concrete_two_by_two_witness` – an explicit noncommutative `2 × 2` integer example:
  `P = E₁₁` is idempotent, `[P, X] ≠ 0`, and the barrier potential `V = -[P,X]²` is `1`.
-/

namespace SouriauMetriplecticAttentionCasimirPoset.MatrixInstance

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [DecidableEq n] in
/-- The matrix trace is a cyclic additive functional. -/
theorem trace_cyclic {R : Type*} [CommRing R] (x y : Matrix n n R) :
    traceAddMonoidHom n R (x * y) = traceAddMonoidHom n R (y * x) := by
  simp only [traceAddMonoidHom_apply]
  exact trace_mul_comm x y

/-- **Theorem 2 for matrices**: the Brockett–Souriau flow conserves `tr W`, `tr W²`, `tr W³`
to first order. -/
theorem matrix_spectral_moments_conserved {R : Type*} [CommRing R] (Ω H W : Matrix n n R) :
    let dW := brockettSouriauWeightFlow Ω H W
    trace dW = 0 ∧ trace (dW * W + W * dW) = 0 ∧
      trace (dW * W * W + W * dW * W + W * W * dW) = 0 := by
  have h := souriau_casimir_invariants_and_metriplectic_degeneracy
    (traceAddMonoidHom n R) trace_cyclic 0 H Ω W 0 0 0 (by simp [comm])
  exact ⟨h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2⟩

/-- **Theorem 4 for matrices**: for Hermitian `P` and `X`, the barrier potential
`V = -[P, X]²` has nonnegative trace, vanishing exactly when `P` and `X` commute. -/
theorem matrix_barrier_potential_nonneg_and_faithful
    {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
    [NoZeroDivisors R]
    (P X : Matrix n n R) (hPs : Pᴴ = P) (hXs : Xᴴ = X) :
    0 ≤ trace (V_barrier P X) ∧ (trace (V_barrier P X) = 0 ↔ comm P X = 0) := by
  have h := barrier_potential_nonneg_and_faithful (traceAddMonoidHom n R)
    (fun Y => (posSemidef_conjTranspose_mul_self Y).trace_nonneg)
    (fun Y hY => trace_conjTranspose_mul_self_eq_zero_iff.mp hY) P X hPs hXs
  exact ⟨h.2.2.1, h.2.2.2⟩

/-- Rank-one projection `E₁₁`. -/
def P₀ : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, 0]

/-- Off-diagonal swap. -/
def X₀ : Matrix (Fin 2) (Fin 2) ℤ := !![0, 1; 1, 0]

/-- A genuinely noncommutative witness: `P₀` is idempotent, does not commute with `X₀`,
and the barrier potential `V = -[P₀, X₀]²` equals the identity. -/
theorem concrete_two_by_two_witness :
    P₀ * P₀ = P₀ ∧ comm P₀ X₀ ≠ 0 ∧ V_barrier P₀ X₀ = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [P₀, Matrix.mul_apply, Fin.sum_univ_two]
  · intro h
    have h01 := congrFun (congrFun h 0) 1
    simp [comm, P₀, X₀] at h01
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [V_barrier, J_barrier, comm, P₀, X₀]

section Hermitian

variable {R : Type*} [CommRing R] [PartialOrder R] [StarRing R] [StarOrderedRing R]
  [NoZeroDivisors R]

/-- **Theorem 7 for matrices**: if `[Ω, H] = 0` and `W, H` are Hermitian, then
`tr (dW · H) ≥ 0` along the Brockett–Souriau flow, with equality iff `[W, H] = 0`. -/
theorem matrix_brockett_souriau_lyapunov
    (Ω H W : Matrix n n R) (hΩH : comm Ω H = 0) (hH : Hᴴ = H) (hW : Wᴴ = W) :
    0 ≤ trace (brockettSouriauWeightFlow Ω H W * H) ∧
      (trace (brockettSouriauWeightFlow Ω H W * H) = 0 ↔ comm W H = 0) := by
  have h := brockett_souriau_lyapunov (traceAddMonoidHom n R) trace_cyclic
    (fun Y => (posSemidef_conjTranspose_mul_self Y).trace_nonneg)
    (fun Y hY => trace_conjTranspose_mul_self_eq_zero_iff.mp hY) Ω H W hΩH hH hW
  exact h.2

end Hermitian

end SouriauMetriplecticAttentionCasimirPoset.MatrixInstance
