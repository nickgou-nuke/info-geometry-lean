/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Quantum.RealificationStates
import InfoGeometry.Quantum.KrausBoundaryDuality
import InfoGeometry.OperatorAlgebra.NoncommutativeKrausChannel

/-!
# Realification of measurements and existing Kraus channels

Both sides use the repository's existing Kraus sum. The real channel is
defined by real matrices alone. Its agreement with the complex channel is
proved from the faithful block embedding, including the state normalization.
-/

noncomputable section

open Matrix
open scoped BigOperators ComplexOrder

namespace InfoGeometry.Quantum.Realification

open InfoGeometry.OperatorAlgebra.NoncommutativeKrausChannel

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι]

/-- Positive effects retain positivity, and a complete POVM remains complete. -/
theorem realify_povm (E : ι → Matrix n n ℂ)
    (hpos : ∀ i, (E i).PosSemidef) (hsum : ∑ i, E i = 1) :
    (∀ i, (realify (E i)).PosSemidef) ∧ ∑ i, realify (E i) = 1 := by
  constructor
  · intro i
    exact (realify_posSemidef_iff _).mpr (hpos i)
  · rw [← realify_sum, hsum, realify_one]

/-- Completeness normalizes the encoded Born readouts. -/
theorem born_readout_sum (E : ι → Matrix n n ℂ) (ρ : Matrix n n ℂ)
    (hsum : ∑ i, E i = 1) (htrace : trace ρ = 1) :
    ∑ i, trace (realify (E i) * state ρ) = 1 := by
  rw [← trace_sum, ← Finset.sum_mul, ← realify_sum, hsum, realify_one, one_mul]
  exact trace_state_eq_one htrace

/-- The existing arbitrary-star-ring Kraus action commutes with realification. -/
theorem realify_krausChannel (V : ι → Matrix n n ℂ) (A : Matrix n n ℂ) :
    realify (krausChannel V A) =
      krausChannel (fun i => realify (V i)) (realify A) := by
  simp only [krausChannel, realify_sum, realify_mul,
    Matrix.star_eq_conjTranspose, realify_star]

/-- Normalized states intertwine the same Kraus action, without an extra factor. -/
theorem state_krausChannel (V : ι → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    state (krausChannel V ρ) =
      krausChannel (fun i => realify (V i)) (state ρ) := by
  unfold state
  rw [realify_krausChannel]
  simp only [krausChannel, Finset.smul_sum, smul_mul_assoc, mul_smul_comm]

/-- Explicit agreement with the existing complex-linear Choi/Kraus owner. -/
theorem state_krausMap [DecidableEq ι]
    (V : ι → Matrix n n ℂ) (ρ : Matrix n n ℂ) :
    state (InfoGeometry.Quantum.Choi.krausMap V ρ) =
      krausChannel (fun i => realify (V i)) (state ρ) :=
  state_krausChannel V ρ

/-- The trace-preserving completeness relation transports in its actual order. -/
theorem realify_kraus_completeness (V : ι → Matrix n n ℂ)
    (hV : ∑ i, star (V i) * V i = 1) :
    ∑ i, star (realify (V i)) * realify (V i) = 1 := by
  have h := congrArg realify hV
  simpa only [realify_sum, realify_mul, Matrix.star_eq_conjTranspose,
    realify_star, realify_one] using h

/-- The real Kraus formula itself preserves positivity on every real input. -/
theorem real_krausChannel_posSemidef {k : Type*} [Fintype k] [DecidableEq k]
    (V : ι → Matrix k k ℝ) {A : Matrix k k ℝ} (hA : A.PosSemidef) :
    (krausChannel V A).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro i _
  exact hA.mul_mul_conjTranspose_same (V i)

/-- A complete encoded channel maps encoded density matrices to density matrices. -/
theorem realified_channel_density [DecidableEq ι]
    (V : ι → Matrix n n ℂ) (ρ : Matrix n n ℂ)
    (hV : ∑ i, star (V i) * V i = 1)
    (hρ : ρ.PosSemidef) (htrace : trace ρ = 1) :
    (krausChannel (fun i => realify (V i)) (state ρ)).PosSemidef ∧
      trace (krausChannel (fun i => realify (V i)) (state ρ)) = 1 := by
  rw [← state_krausMap]
  apply state_density
  · exact InfoGeometry.Quantum.Choi.krausMap_posSemidef V hρ
  · rw [InfoGeometry.Quantum.Choi.trace_krausMap_of_completeness V hV ρ, htrace]

/-- The existing noncommuting spin operators remain noncommuting real operators. -/
theorem realified_spin_noncommute :
    realify InfoGeometry.Algebra.FiniteSpin.J_plus *
        realify InfoGeometry.Algebra.FiniteSpin.J_minus ≠
      realify InfoGeometry.Algebra.FiniteSpin.J_minus *
        realify InfoGeometry.Algebra.FiniteSpin.J_plus := by
  rw [← realify_mul, ← realify_mul]
  exact realify_injective.ne InfoGeometry.Algebra.FiniteSpin.j_plus_j_minus_ne

end InfoGeometry.Quantum.Realification
