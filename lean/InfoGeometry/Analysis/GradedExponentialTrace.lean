/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Data.Matrix.Block
import Mathlib.Topology.UniformSpace.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# Cyclic functionals of genuine operator exponentials

A continuous cyclic functional on a complete normed algebra evaluates
`Gamma * exp (t • D^2)` as `tau Gamma` whenever `Gamma` anticommutes with `D`.
The proof uses the existing algebraic graded cancellation and the convergent
native exponential series. `Gamma` need not be an involution or self-adjoint.

The finite rectangular consequence retains arbitrary ordered matrix products:
`trace (exp (t • (A*B))) - trace (exp (t • (B*A))) = card m - card n`.
It follows from the actual doubled block operator, without diagonalization.
Square-zero factors also give an exponentially weighted commutator trace of
zero, even when the factors do not commute. A different finite weight can
give a nonzero trace, so neither conclusion alone identifies a boundary flux.

The generic functional is supplied as continuous and cyclic. This file does
not construct a trace on all bounded Hilbert operators, an unbounded heat
kernel, an APS boundary problem, or an analytic index.
-/

noncomputable section

namespace InfoGeometry.Analysis.GradedExponentialTrace

open InfoGeometry.OperatorAlgebra.NoncommutativeGradedTrace
open scoped BigOperators

section Algebraic

variable {R K : Type*} [Ring R] [Field K] [CharZero K]

/-- Positive powers of an odd square vanish against a cyclic functional
with its anticommuting weight. No involution or star hypothesis is needed. -/
theorem cyclicFunctional_odd_square_positive_power
    (τ : R →+ K) (hτ : IsCyclic τ) (G D : R)
    (hodd : G * D + D * G = 0) (k : ℕ) :
    τ (G * (D * D) ^ (k + 1)) = 0 := by
  have hD : Commute D (D * D) := by
    show D * (D * D) = (D * D) * D
    exact (mul_assoc D D D).symm
  have hpow := hD.pow_right k
  have hodd' : (G * (D * D) ^ k) * D + D * (G * (D * D) ^ k) = 0 := by
    calc
      (G * (D * D) ^ k) * D + D * (G * (D * D) ^ k) =
          (G * D) * (D * D) ^ k + (D * G) * (D * D) ^ k := by
            rw [mul_assoc G _ D, ← hpow.eq]
            simp only [mul_assoc]
      _ = (G * D + D * G) * (D * D) ^ k := (add_mul _ _ _).symm
      _ = 0 := by rw [hodd, zero_mul]
  have hzero := gradedTrace_odd_square_eq_zero τ hτ
    (fun z hz => (mul_eq_zero.mp (show (2 : K) * z = 0 by
      simpa only [two_mul] using hz)).resolve_left (by norm_num)) hodd'
  simpa only [gradedTrace, pow_succ, mul_assoc] using hzero

/-- A square-zero factor commutes with its anticommutator with any partner.
The partner itself does not need to be square-zero for this identity. -/
theorem commute_anticommutator_of_square_zero (E F : R) (hE : E * E = 0) :
    Commute E (E * F + F * E) := by
  show E * (E * F + F * E) = (E * F + F * E) * E
  calc
    E * (E * F + F * E) = (E * E) * F + (E * F) * E := by
      simp only [mul_add, mul_assoc]
    _ = (E * F) * E := by rw [hE, zero_mul, zero_add]
    _ = (E * F) * E + F * (E * E) := by rw [hE, mul_zero, add_zero]
    _ = (E * F + F * E) * E := by simp only [add_mul, mul_assoc]

end Algebraic

section Banach

variable {𝕜 A : Type*} [RCLike 𝕜] [NormedRing A] [NormedAlgebra 𝕜 A]
  [CompleteSpace A]

/-- Continuity and the genuine convergent exponential series upgrade the
algebraic graded cancellation to an exact exponential identity. -/
theorem cyclicFunctional_exp_odd_square
    (τ : A →L[𝕜] 𝕜) (hτ : IsCyclic τ.toLinearMap.toAddMonoidHom)
    (G D : A) (hodd : G * D + D * G = 0) (t : 𝕜) :
    τ (G * NormedSpace.exp (t • (D * D))) = τ G := by
  let L : A →L[𝕜] 𝕜 := τ.comp (ContinuousLinearMap.mul 𝕜 A G)
  have hs := L.hasSum (NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) (t • (D * D)))
  have hterm (k : ℕ) :
      L (((k.factorial : 𝕜)⁻¹) • (t • (D * D)) ^ k) =
        if k = 0 then τ G else 0 := by
    cases k with
    | zero => simp [L]
    | succ k =>
      have hz : τ (G * (D * D) ^ (k + 1)) = 0 :=
        cyclicFunctional_odd_square_positive_power
          τ.toLinearMap.toAddMonoidHom hτ G D hodd k
      simp only [map_smul, smul_pow, Nat.succ_ne_zero, ite_false]
      change (↑(k + 1).factorial : 𝕜)⁻¹ *
        (t ^ (k + 1) * τ (G * (D * D) ^ (k + 1))) = 0
      rw [hz, mul_zero, mul_zero]
  have hs' : HasSum (fun k : ℕ => if k = 0 then τ G else 0)
      (τ (G * NormedSpace.exp (t • (D * D)))) := by
    simpa only [hterm, L, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.mul_apply'] using hs
  exact hs'.unique (hasSum_ite_eq 0 (τ G))

omit [CompleteSpace A] in
/-- Exponential commutation and the existing cyclic cancellation annihilate
the weighted commutator. Square-zero of the first factor already suffices.
Completeness is not needed for this commutation argument; on complete
algebras, the native exponential additionally has its convergent series. -/
theorem cyclicFunctional_commutator_exp_anticommutator
    (τ : A →+ 𝕜) (hτ : IsCyclic τ) (E F : A) (hE : E * E = 0) (t : 𝕜) :
    τ ((E * F - F * E) * NormedSpace.exp (t • (E * F + F * E))) = 0 := by
  have hc := ((commute_anticommutator_of_square_zero E F hE).smul_right t).exp_right
  calc
    τ ((E * F - F * E) * NormedSpace.exp (t • (E * F + F * E))) =
        τ (NormedSpace.exp (t • (E * F + F * E)) * (E * F - F * E)) := hτ _ _
    _ = 0 := gradedTrace_commutator_eq_zero τ hτ hc.symm.eq

end Banach

section Matrices

variable {𝕜 m n : Type*} [RCLike 𝕜]
  [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]

open scoped Matrix.Norms.Operator

/-- The genuine matrix exponential respects an actual two-block diagonal
operator. Its convergence, including each matrix entry, is supplied by the
native exponential-series theorem; no totalized divergent sum is used. -/
theorem exp_fromBlocks_zero_zero (A : Matrix m m 𝕜) (B : Matrix n n 𝕜) :
    NormedSpace.exp (Matrix.fromBlocks A 0 0 B) =
      Matrix.fromBlocks (NormedSpace.exp A) 0 0 (NormedSpace.exp B) := by
  have hs := NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) (Matrix.fromBlocks A 0 0 B)
  have ha := NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) A
  have hb := NormedSpace.exp_series_hasSum_exp' (𝕂 := 𝕜) B
  ext i j
  have hij := Pi.hasSum.mp (Pi.hasSum.mp hs i) j
  rcases i with i | i <;> rcases j with j | j
  · have h := Pi.hasSum.mp (Pi.hasSum.mp ha i) j
    have hblock : HasSum (fun k : ℕ => ((k.factorial : 𝕜)⁻¹ • A ^ k) i j)
        (NormedSpace.exp (Matrix.fromBlocks A 0 0 B) (Sum.inl i) (Sum.inl j)) := by
      simpa only [Matrix.fromBlocks_diagonal_pow, Matrix.smul_apply,
        Matrix.fromBlocks_apply₁₁] using! hij
    exact hblock.unique h
  · have h : HasSum (fun _ : ℕ => (0 : 𝕜))
        (NormedSpace.exp (Matrix.fromBlocks A 0 0 B) (Sum.inl i) (Sum.inr j)) := by
      simpa only [Matrix.fromBlocks_diagonal_pow, Matrix.smul_apply,
        Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, smul_zero] using! hij
    exact h.unique hasSum_zero
  · have h : HasSum (fun _ : ℕ => (0 : 𝕜))
        (NormedSpace.exp (Matrix.fromBlocks A 0 0 B) (Sum.inr i) (Sum.inl j)) := by
      simpa only [Matrix.fromBlocks_diagonal_pow, Matrix.smul_apply,
        Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, smul_zero] using! hij
    exact h.unique hasSum_zero
  · have h := Pi.hasSum.mp (Pi.hasSum.mp hb i) j
    have hblock : HasSum (fun k : ℕ => ((k.factorial : 𝕜)⁻¹ • B ^ k) i j)
        (NormedSpace.exp (Matrix.fromBlocks A 0 0 B) (Sum.inr i) (Sum.inr j)) := by
      simpa only [Matrix.fromBlocks_diagonal_pow, Matrix.smul_apply,
        Matrix.fromBlocks_apply₂₂] using! hij
    exact hblock.unique h

/-- Rectangular partners have exponential traces differing exactly by the
dimension defect. The proof uses their doubled operator and native block
transport; neither partner is assumed diagonal, self-adjoint, or invertible. -/
theorem rectangular_exponential_trace_difference
    (A : Matrix m n 𝕜) (B : Matrix n m 𝕜) (t : 𝕜) :
    Matrix.trace (NormedSpace.exp (t • (A * B))) -
        Matrix.trace (NormedSpace.exp (t • (B * A))) =
      (Fintype.card m : 𝕜) - (Fintype.card n : 𝕜) := by
  let G : Matrix (m ⊕ n) (m ⊕ n) 𝕜 := Matrix.fromBlocks 1 0 0 (-1)
  let D : Matrix (m ⊕ n) (m ⊕ n) 𝕜 := Matrix.fromBlocks 0 A B 0
  let τ : Matrix (m ⊕ n) (m ⊕ n) 𝕜 →L[𝕜] 𝕜 :=
    { toLinearMap := Matrix.traceLinearMap (m ⊕ n) 𝕜 𝕜
      cont := by
        change Continuous (fun M : Matrix (m ⊕ n) (m ⊕ n) 𝕜 => ∑ i, M i i)
        fun_prop }
  have hcyclic : IsCyclic τ.toLinearMap.toAddMonoidHom :=
    fun X Y => Matrix.trace_mul_comm X Y
  have hodd : G * D + D * G = 0 := by
    simp [G, D, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  have hsquare : D * D = Matrix.fromBlocks (A * B) 0 0 (B * A) := by
    simp [D, Matrix.fromBlocks_multiply]
  have h := cyclicFunctional_exp_odd_square τ hcyclic G D hodd t
  change Matrix.trace (G * NormedSpace.exp (t • (D * D))) = Matrix.trace G at h
  rw [hsquare, Matrix.fromBlocks_smul, smul_zero, smul_zero,
    exp_fromBlocks_zero_zero] at h
  simp only [G, Matrix.fromBlocks_multiply, one_mul, neg_mul] at h
  simp only [Matrix.trace, Matrix.diag_apply, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂] at h
  simpa [Matrix.trace, sub_eq_add_neg] using h

/-- The matrix specialization retains arbitrary ordered products. A single
square-zero factor suffices for the exponential weighted trace to vanish. -/
theorem trace_commutator_exp_anticommutator
    (E F : Matrix n n 𝕜) (hE : E * E = 0) (t : 𝕜) :
    Matrix.trace ((E * F - F * E) * NormedSpace.exp (t • (E * F + F * E))) = 0 :=
  cyclicFunctional_commutator_exp_anticommutator
    (Matrix.traceLinearMap n 𝕜 𝕜).toAddMonoidHom
    (fun X Y => Matrix.trace_mul_comm X Y) E F hE t

/-- A genuinely noncommuting pair of nilpotents has zero exponential
weighted commutator trace for every parameter. The different finite weight
`E*F` gives trace one, without any boundary or infinite-dimensional limit. -/
theorem noncommuting_nilpotents_distinguish_weights :
    ∃ E F : Matrix (Fin 2) (Fin 2) ℝ,
      E * F ≠ F * E ∧ E * E = 0 ∧ F * F = 0 ∧
      Matrix.trace ((E * F - F * E) * (E * F)) = 1 ∧
      ∀ t : ℝ, Matrix.trace
        ((E * F - F * E) * NormedSpace.exp (t • (E * F + F * E))) = 0 := by
  let E : Matrix (Fin 2) (Fin 2) ℝ := !![0, 1; 0, 0]
  let F : Matrix (Fin 2) (Fin 2) ℝ := !![0, 0; 1, 0]
  have hE : E * E = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [E, Matrix.mul_apply, Fin.sum_univ_two]
  have hF : F * F = 0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [F, Matrix.mul_apply, Fin.sum_univ_two]
  refine ⟨E, F, ?_, hE, hF, ?_, fun t => trace_commutator_exp_anticommutator E F hE t⟩
  · intro h
    have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℝ => M 0 0) h
    norm_num [E, F, Matrix.mul_apply, Fin.sum_univ_two] at hentry
  · norm_num [E, F, Matrix.trace, Matrix.mul_apply, Fin.sum_univ_two]

end Matrices

end InfoGeometry.Analysis.GradedExponentialTrace
