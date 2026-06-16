import Mathlib
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Primon Gas Thermodynamics — finite prime set partition function

For a finite set of primes S, the bosonic partition function is:
  Z_b(β) = Π_{p∈S} (1 - p^{-β})^{-1}

The fermionic (graded) partition function is:
  Z_f(β) = Π_{p∈S} (1 + p^{-β})

Reference: Bost–Connes (1995), Section 2.
-/

open Real
open Finset

noncomputable section

namespace InfoGeometry.Arithmetic.PrimonThermodynamics

noncomputable def bosonFactor (p : ℕ) (β : ℝ) : ℝ :=
  (1 - ((p : ℝ) ^ (-β)))⁻¹

noncomputable def fermionFactor (p : ℕ) (β : ℝ) : ℝ :=
  1 + ((p : ℝ) ^ (-β))

noncomputable def bosonPartition (S : Finset ℕ) (β : ℝ) : ℝ :=
  ∏ p ∈ S, bosonFactor p β

noncomputable def fermionPartition (S : Finset ℕ) (β : ℝ) : ℝ :=
  ∏ p ∈ S, fermionFactor p β

/-- Supersymmetric partition: Z_s = Z_b · Z_f = Π (1 + p^{-β})/(1 - p^{-β}) -/
noncomputable def superPartition (S : Finset ℕ) (β : ℝ) : ℝ :=
  bosonPartition S β * fermionPartition S β

@[simp] theorem bosonPartition_empty (β : ℝ) : bosonPartition ∅ β = 1 := by
  simp [bosonPartition]

@[simp] theorem fermionPartition_empty (β : ℝ) : fermionPartition ∅ β = 1 := by
  simp [fermionPartition]

theorem bosonPartition_singleton (p : ℕ) (β : ℝ) :
    bosonPartition {p} β = bosonFactor p β := by
  simp [bosonPartition]

theorem fermionPartition_singleton (p : ℕ) (β : ℝ) :
    fermionPartition {p} β = fermionFactor p β := by
  simp [fermionPartition]

/-- Partition functions are multiplicative over disjoint unions. -/
theorem bosonPartition_union (S T : Finset ℕ) (h : Disjoint S T) (β : ℝ) :
    bosonPartition (S ∪ T) β = bosonPartition S β * bosonPartition T β := by
  simp [bosonPartition, Finset.prod_union h]

/-- For a finite set of primes, the partition function is the product of
    single-mode factors. -/
theorem bosonPartition_eq_prod (S : Finset ℕ) (β : ℝ) :
    bosonPartition S β = ∏ p ∈ S, (1 - ((p : ℝ) ^ (-β)))⁻¹ := by
  simp [bosonPartition, bosonFactor]

/-- The bosonic internal energy: U = -∂/∂β log Z = Σ (log p)·p^{-β}/(1-p^{-β}) -/
noncomputable def bosonInternalEnergy (S : Finset ℕ) (β : ℝ) : ℝ :=
  ∑ p ∈ S, Real.log (p : ℝ) * ((p : ℝ) ^ (-β)) * bosonFactor p β

/-- The bosonic free energy: F = -(1/β)·log Z -/
noncomputable def bosonFreeEnergy (S : Finset ℕ) (β : ℝ) : ℝ :=
  -(1 / β) * Real.log (bosonPartition S β)

/-- Witten index for finite S: Z_f · Z_b = Π (fermion · boson). -/
theorem witten_index_finite (S : Finset ℕ) (β : ℝ) :
    fermionPartition S β * bosonPartition S β =
    ∏ p ∈ S, (fermionFactor p β * bosonFactor p β) := by
  rw [fermionPartition, bosonPartition]
  simp [Finset.prod_mul_distrib, mul_comm]

/-- The supersymmetric partition cancels to Π (1 + p^{-β})/(1 - p^{-β}).
    For each p, the factor is (1+p^{-β})/(1-p^{-β}) = coth(β·log p / 2). -/
theorem superPartition_eq (S : Finset ℕ) (β : ℝ) :
    superPartition S β = ∏ p ∈ S, (fermionFactor p β * bosonFactor p β) := by
  rw [superPartition, fermionPartition, bosonPartition]
  simp [Finset.prod_mul_distrib, mul_comm]

end InfoGeometry.Arithmetic.PrimonThermodynamics
