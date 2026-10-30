/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.NCG.NonCommutativeFredholmIndex
import InfoGeometry.Core.PeirceGrading

/-! Weighted trace identities on full matrix algebras. No fixed basis grading,
positivity, or spectral-triple structure is assumed. -/

namespace InfoGeometry.NCG.ChiralMatrixTrace

open Matrix NonCommutativeFredholmIndex
open InfoGeometry.Core.PeirceGrading

variable {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]

/-- Conjugation by an involutive chirality reverses an odd Dirac operator.
The statement is for arbitrary noncommuting matrix operators. -/
theorem dirac_conjugation_by_chirality
    {γ D : Matrix n n R}
    (hγsq : γ * γ = 1)
    (hγD : anticommutator γ D = 0) :
    γ * D * γ = -D := by
  have hsum : γ * D + D * γ = 0 := by
    simpa [NonCommutativeFredholmIndex.anticommutator, add_comm] using hγD
  have hsum' : D * γ + γ * D = 0 := by simpa [add_comm] using hsum
  have hDγ : γ * D = -(D * γ) := eq_neg_of_add_eq_zero_right hsum'
  calc
    γ * D * γ = (-(D * γ)) * γ := by rw [hDγ]
    _ = -(D * (γ * γ)) := by simp only [Matrix.neg_mul, Matrix.mul_assoc]
    _ = -(D * 1) := by rw [hγsq]
    _ = -D := by simp

/-- The square of an odd Dirac operator is even: chirality commutes with `D²`.
This is an operator identity and uses no diagonal form or spectral
decomposition. -/
theorem dirac_square_commutes_with_chirality
    {γ D : Matrix n n R}
    (hγD : anticommutator γ D = 0) :
    commutator γ (D * D) = 0 := by
  have hDγ : D * γ = -(γ * D) := eq_neg_of_add_eq_zero_right hγD
  dsimp [NonCommutativeFredholmIndex.commutator]
  calc
    γ * (D * D) - (D * D) * γ = γ * (D * D) + D * (γ * D) := by
      rw [mul_assoc D D γ, hDγ, mul_neg, sub_neg_eq_add]
    _ = 0 := by
      calc
        γ * (D * D) + D * (γ * D) = (γ * D) * D + (D * γ) * D := by
          simp only [← mul_assoc]
        _ = 0 := by
          have hmul := congrArg (fun Z : Matrix n n R => Z * D) hγD
          dsimp [NonCommutativeFredholmIndex.anticommutator] at hmul
          simpa only [add_mul, zero_mul, ← mul_assoc] using hmul

/-- Operator-valued divergence for a finite family of generators and fluxes. -/
def operatorDivergence {κ : Type*} [Fintype κ]
    (H J : κ → Matrix n n R) : Matrix n n R :=
  ∑ i, commutator (H i) (J i)

/-- The trace of the operator-valued inner-derivation divergence vanishes by
cyclicity, while the divergence itself remains a matrix operator. -/
theorem trace_operatorDivergence_zero {κ : Type*} [Fintype κ]
    (H J : κ → Matrix n n R) :
    trace (operatorDivergence H J) = 0 := by
  simp [operatorDivergence, NonCommutativeFredholmIndex.trace_commutator_zero]

/-- Taking the flux in each direction to be its inner gradient yields the
noncommutative sum of double commutators. -/
theorem operatorDivergence_innerGradient {κ : Type*} [Fintype κ]
    (H : κ → Matrix n n R) (X : Matrix n n R) :
    operatorDivergence H (fun i => commutator (H i) X) =
      ∑ i, commutator (H i) (commutator (H i) X) := rfl

/-- Quadratic Casimir operator assembled from a finite family of generators. -/
def operatorCasimir {κ : Type*} [Fintype κ]
    (H : κ → Matrix n n R) : Matrix n n R :=
  ∑ i, H i * H i

/-- The Casimir commutator expands as the sum of the generator-level
commutators, without assuming that the generators commute. -/
theorem operatorCasimir_commutator {κ : Type*} [Fintype κ]
    (H : κ → Matrix n n R) (k : κ) :
    commutator (H k) (operatorCasimir H) =
      ∑ i, commutator (H k) (H i * H i) := by
  unfold NonCommutativeFredholmIndex.commutator operatorCasimir
  simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]

/-- The commutator moves from the test matrix to the trace weight. -/
theorem trace_commutator_transport (γ A X : Matrix n n R) :
    trace (γ * commutator A X) = trace (commutator γ A * X) := by
  simp only [NonCommutativeFredholmIndex.commutator, mul_sub, sub_mul, trace_sub, ← mul_assoc]
  rw [trace_mul_cycle γ X A]

/-- The same transport holds for the anticommutator, with no grading hypotheses. -/
theorem trace_anticommutator_transport (γ D X : Matrix n n R) :
    trace (γ * anticommutator D X) = trace (anticommutator γ D * X) := by
  simp only [anticommutator, mul_add, add_mul, trace_add, ← mul_assoc]
  rw [trace_mul_cycle γ X D]

/-- Chiral cancellation holds for every test matrix, irrespective of its parity. -/
theorem trace_anticommutator_zero {γ D : Matrix n n R}
    (h : anticommutator γ D = 0) (X : Matrix n n R) :
    trace (γ * anticommutator D X) = 0 := by
  rw [trace_anticommutator_transport, h, zero_mul, trace_zero]

/-- Vanishing on every anticommutator detects the actual chiral equation. -/
theorem trace_anticommutator_zero_iff (γ D : Matrix n n R) :
    (∀ X, trace (γ * anticommutator D X) = 0) ↔ anticommutator γ D = 0 := by
  constructor
  · intro h
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro X
    simpa only [zero_mul, trace_zero, ← trace_anticommutator_transport] using h X
  · intro h X
    exact trace_anticommutator_zero h X

/-- The trace pairing detects exactly the centralizer of the weight. -/
theorem trace_commutator_zero_iff (γ A : Matrix n n R) :
    (∀ X, trace (γ * commutator A X) = 0) ↔ Commute γ A := by
  constructor
  · intro h
    apply sub_eq_zero.mp
    apply Matrix.ext_iff_trace_mul_right.mpr
    intro X
    change trace (NonCommutativeFredholmIndex.commutator γ A * X) = trace (0 * X)
    rw [← trace_commutator_transport, zero_mul, trace_zero]
    exact h X
  · intro h X
    rw [trace_commutator_transport]
    simp only [NonCommutativeFredholmIndex.commutator, h.eq, sub_self, zero_mul, trace_zero]

/-- The Peirce pinching is self-adjoint for the bilinear matrix trace pairing. -/
theorem trace_even_adjoint (P γ X : Matrix n n R) :
    trace (γ * even P X) = trace (even P γ * X) := by
  simp only [even_apply, mul_add, add_mul, trace_add]
  congr 1
  · calc
      _ = trace ((γ * P * X) * P) := by simp only [mul_assoc]
      _ = trace (P * (γ * P * X)) := trace_mul_comm _ _
      _ = _ := by simp only [mul_assoc]
  · calc
      _ = trace ((γ * (1 - P) * X) * (1 - P)) := by simp only [mul_assoc]
      _ = trace ((1 - P) * (γ * (1 - P) * X)) := trace_mul_comm _ _
      _ = _ := by simp only [mul_assoc]

/-- A weighted trace is invariant under this pinching for every test matrix exactly for commuting weights. -/
theorem trace_even_invariant_iff {P : Matrix n n R} (hP : IsIdempotentElem P)
    (γ : Matrix n n R) :
    (∀ X, trace (γ * even P X) = trace (γ * X)) ↔ Commute P γ := by
  simp_rw [trace_even_adjoint]
  rw [← Matrix.ext_iff_trace_mul_right]
  rw [← LinearMap.IsIdempotentElem.mem_range_iff (even_idempotent hP), mem_even_iff hP]
  rfl

/-- The discarded component is invisible to a commuting trace weight. -/
theorem trace_odd_zero {P γ : Matrix n n R} (hP : IsIdempotentElem P)
    (hγ : Commute P γ) (X : Matrix n n R) : trace (γ * odd P X) = 0 := by
  have he := (trace_even_invariant_iff hP γ).2 hγ X
  simp only [odd, LinearMap.sub_apply, LinearMap.id_apply, mul_sub, trace_sub, he,
    sub_self]

/-- Two idempotent commutators have an even product in the native Peirce range. -/
theorem commutator_product_mem_even {P : Matrix n n R} (hP : IsIdempotentElem P)
    (X Y : Matrix n n R) :
    commutator P X * commutator P Y ∈ LinearMap.range (even P) :=
  odd_mul_odd hP (commutator_odd hP X) (commutator_odd hP Y)

/-- Without cancellation of two, the doubled weighted trace is what vanishes. -/
theorem two_trace_mul_eq_zero {γ D B : Matrix n n R}
    (hγ : anticommutator γ D = 0) (hDB : Commute D B) :
    trace (γ * (D * B)) + trace (γ * (D * B)) = 0 := by
  have h := trace_anticommutator_zero hγ B
  simpa only [anticommutator, ← hDB.eq, mul_add, trace_add] using h

/-- Cancellation on the regular factor requires no additive two-torsion. -/
theorem trace_mul_eq_zero [IsAddTorsionFree R] {γ D B : Matrix n n R}
    (hγ : anticommutator γ D = 0) (hDB : Commute D B) :
    trace (γ * (D * B)) = 0 := by
  apply IsAddTorsionFree.nsmul_right_injective (by decide : (2 : ℕ) ≠ 0)
  simpa only [two_nsmul, smul_zero] using two_trace_mul_eq_zero hγ hDB

end InfoGeometry.NCG.ChiralMatrixTrace
