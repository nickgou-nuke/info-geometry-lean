/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import InfoGeometry.OperatorAlgebra.MatrixTraceGeometry
import Mathlib.Algebra.Algebra.Subalgebra.Centralizer

/-!
# Centralizers and quadratic invariance in the full matrix algebra

Conservation is membership in the native centralizer subalgebra. A quadratic
sum is invariant when the inner action on its generators has skew-symmetric
coefficients. The proof cancels the two finite indices and does not require
the generators to commute. The quadratic matrix is distinguished from the
double-commutator operator acting on arbitrary matrices.
-/

namespace InfoGeometry.OperatorAlgebra.MatrixConservation

open Matrix
open scoped BigOperators

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n ι : Type*} [Fintype n] [DecidableEq n]

/-- The native family centralizer is exactly the common kernel of the inner
Lie actions. No faithfulness of the adjoint representation is assumed. -/
theorem mem_centralizer_range_iff_ad (H : ι → Matrix n n ℂ)
    (A : Matrix n n ℂ) :
    A ∈ Subalgebra.centralizer ℂ (Set.range H) ↔
      ∀ i, LieAlgebra.ad ℂ (Matrix n n ℂ) (H i) A = 0 := by
  constructor
  · intro h i
    change H i * A - A * H i = 0
    exact sub_eq_zero.mpr ((Subalgebra.mem_centralizer_iff.mp h) (H i) ⟨i, rfl⟩)
  · intro h
    apply Subalgebra.mem_centralizer_iff.mpr
    rintro _ ⟨i, rfl⟩
    exact sub_eq_zero.mp (h i)

/-- Multiplication preserves conservation under every generator in a family. -/
theorem ad_mul_eq_zero (H : ι → Matrix n n ℂ) (A B : Matrix n n ℂ)
    (hA : ∀ i, LieAlgebra.ad ℂ (Matrix n n ℂ) (H i) A = 0)
    (hB : ∀ i, LieAlgebra.ad ℂ (Matrix n n ℂ) (H i) B = 0) :
    ∀ i, LieAlgebra.ad ℂ (Matrix n n ℂ) (H i) (A * B) = 0 := by
  apply (mem_centralizer_range_iff_ad H (A * B)).mp
  exact (Subalgebra.centralizer ℂ (Set.range H)).mul_mem
    ((mem_centralizer_range_iff_ad H A).mpr hA)
    ((mem_centralizer_range_iff_ad H B).mpr hB)

/-- The native Lie product stays in the same family centralizer. -/
theorem lie_mem_centralizer {H : ι → Matrix n n ℂ} {A B : Matrix n n ℂ}
    (hA : A ∈ Subalgebra.centralizer ℂ (Set.range H))
    (hB : B ∈ Subalgebra.centralizer ℂ (Set.range H)) :
    ⁅A, B⁆ ∈ Subalgebra.centralizer ℂ (Set.range H) := by
  change A * B - B * A ∈ Subalgebra.centralizer ℂ (Set.range H)
  exact (Subalgebra.centralizer ℂ (Set.range H)).sub_mem
    ((Subalgebra.centralizer ℂ (Set.range H)).mul_mem hA hB)
    ((Subalgebra.centralizer ℂ (Set.range H)).mul_mem hB hA)

/-- The symmetric product also stays in the family centralizer. -/
theorem anticommutator_mem_centralizer {H : ι → Matrix n n ℂ}
    {A B : Matrix n n ℂ}
    (hA : A ∈ Subalgebra.centralizer ℂ (Set.range H))
    (hB : B ∈ Subalgebra.centralizer ℂ (Set.range H)) :
    A * B + B * A ∈ Subalgebra.centralizer ℂ (Set.range H) := by
  exact (Subalgebra.centralizer ℂ (Set.range H)).add_mem
    ((Subalgebra.centralizer ℂ (Set.range H)).mul_mem hA hB)
    ((Subalgebra.centralizer ℂ (Set.range H)).mul_mem hB hA)

variable [Fintype ι]

/-- Skew coefficients contract to zero against the symmetric ordered products.
The cancellation uses only a swap of the two finite indices. -/
theorem skew_quadratic_sum_eq_zero (H : ι → Matrix n n ℂ)
    (c : ι → ι → ℂ) (hc : ∀ i j, c i j = -c j i) :
    (∑ i, ∑ j, c i j • (H j * H i + H i * H j)) = 0 := by
  let S := ∑ i, ∑ j, c i j • (H j * H i + H i * H j)
  have hneg : S = -S := by
    calc
      S = ∑ i, ∑ j, c j i • (H i * H j + H j * H i) := Finset.sum_comm
      _ = ∑ i, ∑ j, -(c i j • (H j * H i + H i * H j)) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hc j i, neg_smul, add_comm (H i * H j) (H j * H i)]
      _ = -S := by simp only [S, Finset.sum_neg_distrib]
  have htwo : (2 : ℂ) • S = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr hneg
  exact (smul_eq_zero.mp htwo).resolve_left two_ne_zero

/-- A skew coefficient action preserves the quadratic sum even when the
generators themselves do not commute. -/
theorem commute_quadratic_sum (K : Matrix n n ℂ) (H : ι → Matrix n n ℂ)
    (c : ι → ι → ℂ)
    (haction : ∀ i, ⁅K, H i⁆ = ∑ j, c i j • H j)
    (hskew : ∀ i j, c i j = -c j i) :
    Commute K (∑ i, H i * H i) := by
  have hbracket : ⁅K, ∑ i, H i * H i⁆ =
      ∑ i, ∑ j, c i j • (H j * H i + H i * H j) := by
    rw [lie_sum]
    simp_rw [MatrixOperatorIdentities.lie_mul, haction]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_mul_assoc, mul_smul_comm, smul_add]
  change K * (∑ i, H i * H i) = (∑ i, H i * H i) * K
  apply sub_eq_zero.mp
  change ⁅K, ∑ i, H i * H i⁆ = 0
  rw [hbracket]
  exact skew_quadratic_sum_eq_zero H c hskew

/-- Applying the skew-action criterion to every generator places the quadratic
sum in the native family centralizer, with no ambient centrality claim. -/
theorem quadratic_sum_mem_centralizer (H : ι → Matrix n n ℂ)
    (c : ι → ι → ι → ℂ)
    (haction : ∀ k i, ⁅H k, H i⁆ = ∑ j, c k i j • H j)
    (hskew : ∀ k i j, c k i j = -c k j i) :
    (∑ i, H i * H i) ∈ Subalgebra.centralizer ℂ (Set.range H) := by
  apply Subalgebra.mem_centralizer_iff.mpr
  rintro _ ⟨k, rfl⟩
  exact commute_quadratic_sum (H k) H (c k) (haction k) (hskew k)

/-- Cyclic trace annihilates every finite sum of inner-divergence terms. -/
theorem trace_sum_lie_zero (H J : ι → Matrix n n ℂ) :
    trace (∑ i, ⁅H i, J i⁆) = 0 := by
  simp only [trace_sum, MatrixTraceGeometry.trace_lie_zero, Finset.sum_const_zero]

/-- Every weight in the joint centralizer annihilates the trace of the
operator divergence, even when neither the fluxes nor the generators commute. -/
theorem trace_centralizer_mul_sum_lie_zero (H J : ι → Matrix n n ℂ)
    (C : Matrix n n ℂ) (hC : C ∈ Subalgebra.centralizer ℂ (Set.range H)) :
    trace (C * (∑ i, ⁅H i, J i⁆)) = 0 := by
  rw [Finset.mul_sum, trace_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hc : ⁅H i, C⁆ = 0 :=
    sub_eq_zero.mpr ((Subalgebra.mem_centralizer_iff.mp hC) (H i) ⟨i, rfl⟩)
  have ht := MatrixTraceGeometry.trace_lie_mul (H i) C (J i)
  rw [hc, zero_mul, trace_zero] at ht
  exact neg_eq_zero.mp ht.symm

/-- The double-commutator operator includes a two-sided transport term; it is
not multiplication by the quadratic matrix. -/
theorem sum_double_lie_expansion (H : ι → Matrix n n ℂ) (X : Matrix n n ℂ) :
    (∑ i, ⁅H i, ⁅H i, X⁆⁆) =
      (∑ i, H i * H i) * X + X * (∑ i, H i * H i) -
        (2 : ℂ) • (∑ i, H i * X * H i) := by
  simp_rw [MatrixOperatorIdentities.lie_lie_expansion]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.smul_sum]
  abel

/-- Hilbert--Schmidt integration by parts identifies the double commutator
with the sum of pairings of first commutators. -/
theorem trace_star_sum_double_lie (H : ι → Matrix n n ℂ)
    (hH : ∀ i, IsSelfAdjoint (H i)) (A B : Matrix n n ℂ) :
    trace (star A * (∑ i, ⁅H i, ⁅H i, B⁆⁆)) =
      ∑ i, trace (star ⁅H i, A⁆ * ⁅H i, B⁆) := by
  rw [Finset.mul_sum, trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (MatrixTraceGeometry.trace_star_lie_of_isSelfAdjoint
    (hH i) A ⁅H i, B⁆).symm

end InfoGeometry.OperatorAlgebra.MatrixConservation
