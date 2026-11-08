import InfoGeometry.Arithmetic.HoradamIonBinetSlice
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Horadam `2^k`-ion summation slice

This module formalizes a finite, cleared-denominator version of the summation
formula from `preprints201906.0303.v1`, *Horadam 2^k-ions*.

For the Binet core `Cᵢ = A α^i - B β^i`, it proves

`(1-α)(1-β) ∑_{i=0}^n Cᵢ =
  A(1-β)(1-α^(n+1)) - B(1-α)(1-β^(n+1))`.

The coordinate-lift theorem proves the same finite identity componentwise for
`2^k`-ion coordinate packets.

No infinite generating-function convergence, division by `1-α`/`1-β`,
Cayley-Dickson multiplication, Catalan/Cassini identity, or norm theorem is
asserted here.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.HoradamIonSummationSlice

open Finset
open InfoGeometry.Arithmetic.HoradamIonMatrixMethods
open InfoGeometry.Arithmetic.HoradamIonBinetSlice

variable {R : Type*} [CommRing R]

/-- Finite geometric partial sum `∑_{i=0}^n x^i`. -/
def geomPartial (x : R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range (n + 1), x ^ i

/-- Cleared-denominator finite geometric sum identity. -/
theorem one_sub_mul_geomPartial (x : R) (n : ℕ) :
    (1 - x) * geomPartial x n = 1 - x ^ (n + 1) := by
  unfold geomPartial
  have h := mul_geom_sum x (n + 1)
  calc
    (1 - x) * (∑ i ∈ Finset.range (n + 1), x ^ i)
        = -((x - 1) * (∑ i ∈ Finset.range (n + 1), x ^ i)) := by ring
    _ = -(x ^ (n + 1) - 1) := by rw [h]
    _ = 1 - x ^ (n + 1) := by ring

/-- Finite partial sum of the Binet core. -/
def binetPartialSum (A B α β : R) (n : ℕ) : R :=
  ∑ i ∈ Finset.range (n + 1), binetCore A B α β i

/-- Cleared-denominator finite summation formula for the Binet core. -/
theorem binetPartialSum_clear_denominator
    (A B α β : R) (n : ℕ) :
    (1 - α) * (1 - β) * binetPartialSum A B α β n =
      A * (1 - β) * (1 - α ^ (n + 1)) -
        B * (1 - α) * (1 - β ^ (n + 1)) := by
  unfold binetPartialSum binetCore
  rw [Finset.sum_sub_distrib]
  have hα := one_sub_mul_geomPartial (R := R) α n
  have hβ := one_sub_mul_geomPartial (R := R) β n
  unfold geomPartial at hα hβ
  have hAα : (∑ x ∈ Finset.range (n + 1), A * α ^ x) =
      A * (∑ x ∈ Finset.range (n + 1), α ^ x) := by
    rw [Finset.mul_sum]
  have hBβ : (∑ x ∈ Finset.range (n + 1), B * β ^ x) =
      B * (∑ x ∈ Finset.range (n + 1), β ^ x) := by
    rw [Finset.mul_sum]
  rw [hAα, hBβ]
  calc
    (1 - α) * (1 - β) *
        (A * (∑ x ∈ Finset.range (n + 1), α ^ x) -
          B * (∑ x ∈ Finset.range (n + 1), β ^ x))
        = A * (1 - β) * ((1 - α) * (∑ x ∈ Finset.range (n + 1), α ^ x)) -
            B * (1 - α) * ((1 - β) * (∑ x ∈ Finset.range (n + 1), β ^ x)) := by
          ring_nf
    _ = A * (1 - β) * (1 - α ^ (n + 1)) -
          B * (1 - α) * (1 - β ^ (n + 1)) := by
          rw [hα, hβ]

/-- Coordinate partial sum of the Binet ion packet. -/
def binetIonPartialSum {N : ℕ} (A B α β : R) (n : ℕ) : Ion N R :=
  fun s => ∑ i ∈ Finset.range (n + 1), binetCore A B α β (i + s.val)

/-- Componentwise finite summation formula for the coordinate lift. -/
theorem binetIonPartialSum_clear_denominator {N : ℕ}
    (A B α β : R) (n : ℕ) :
    ionScale ((1 - α) * (1 - β)) (binetIonPartialSum (N := N) A B α β n) =
      fun s =>
        A * (1 - β) * α ^ s.val * (1 - α ^ (n + 1)) -
          B * (1 - α) * β ^ s.val * (1 - β ^ (n + 1)) := by
  ext s
  simp [binetIonPartialSum, ionScale, binetCore]
  have hα := one_sub_mul_geomPartial (R := R) α n
  have hβ := one_sub_mul_geomPartial (R := R) β n
  unfold geomPartial at hα hβ
  calc
    (1 - α) * (1 - β) *
        ((∑ x ∈ Finset.range (n + 1), A * α ^ (x + s.val)) -
          ∑ x ∈ Finset.range (n + 1), B * β ^ (x + s.val))
        = A * (1 - β) * α ^ s.val *
              ((1 - α) * (∑ x ∈ Finset.range (n + 1), α ^ x)) -
            B * (1 - α) * β ^ s.val *
              ((1 - β) * (∑ x ∈ Finset.range (n + 1), β ^ x)) := by
          rw [show (∑ x ∈ Finset.range (n + 1), A * α ^ (x + s.val)) =
              A * α ^ s.val * (∑ x ∈ Finset.range (n + 1), α ^ x) by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x hx
                rw [pow_add]
                ring]
          rw [show (∑ x ∈ Finset.range (n + 1), B * β ^ (x + s.val)) =
              B * β ^ s.val * (∑ x ∈ Finset.range (n + 1), β ^ x) by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro x hx
                rw [pow_add]
                ring]
          ring
    _ = A * (1 - β) * α ^ s.val * (1 - α ^ (n + 1)) -
          B * (1 - α) * β ^ s.val * (1 - β ^ (n + 1)) := by
          rw [hα, hβ]

/-- Consolidated finite summation slice packet. -/
theorem horadam_ion_summation_slice_packet {N : ℕ}
    (A B α β : R) :
    (∀ n : ℕ,
      (1 - α) * (1 - β) * binetPartialSum A B α β n =
        A * (1 - β) * (1 - α ^ (n + 1)) -
          B * (1 - α) * (1 - β ^ (n + 1))) ∧
    (∀ n : ℕ,
      ionScale ((1 - α) * (1 - β)) (binetIonPartialSum (N := N) A B α β n) =
        fun s =>
          A * (1 - β) * α ^ s.val * (1 - α ^ (n + 1)) -
            B * (1 - α) * β ^ s.val * (1 - β ^ (n + 1))) := by
  exact ⟨binetPartialSum_clear_denominator A B α β,
    binetIonPartialSum_clear_denominator A B α β⟩

end InfoGeometry.Arithmetic.HoradamIonSummationSlice

end noncomputable section
