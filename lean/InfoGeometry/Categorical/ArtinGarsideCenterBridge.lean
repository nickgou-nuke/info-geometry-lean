import Mathlib.Tactic

import InfoGeometry.Categorical.BraidThreePresentedGroup
import InfoGeometry.Categorical.BraidGroup3S3QuotientBridge
import InfoGeometry.Exceptional.G2ArtinPresentation

/-!
# Artin Garside centers and the B₃ / I₂(6) parity distinction

For the ordinary three-strand braid group B₃ = A₂, the Garside element

  Δ = σ₁ σ₂ σ₁

interchanges the two Artin generators by conjugation, so Δ² is central.

For the dihedral Artin group I₂(6) attached to G₂, the alternating Garside
word has even length six.  In that case the Garside element itself commutes
with both generators and is central.

The module also records the elementary nilpotent-square identity
  (1 + N)² = 1 + 2N
under N² = 0, which is the exact algebraic content behind unipotent
double-braid/shear calculations.

No LogCFT, holonomy, spin-cover, or physical monodromy identification is
asserted here.
-/

namespace InfoGeometry.Categorical.ArtinGarsideCenterBridge

open InfoGeometry.Categorical.BraidThreePresentedGroup
open InfoGeometry.Categorical.BraidGroup3S3QuotientBridge

/-! ## B₃ = A₂: odd Coxeter length, Δ flips generators -/

/-- The B₃ Garside element flips the first generator to the second on the right. -/
theorem b3_garside_mul_sigmaOne :
    garsideDelta * sigmaOne = sigmaTwo * garsideDelta := by
  calc
    garsideDelta * sigmaOne
        = (sigmaOne * sigmaTwo * sigmaOne) * sigmaOne := by rfl
    _ = (sigmaTwo * sigmaOne * sigmaTwo) * sigmaOne := by
      rw [artin_relation]
    _ = sigmaTwo * (sigmaOne * sigmaTwo * sigmaOne) := by
      simp only [mul_assoc]
    _ = sigmaTwo * garsideDelta := by rfl

/-- The B₃ Garside element flips the second generator to the first on the right. -/
theorem b3_garside_mul_sigmaTwo :
    garsideDelta * sigmaTwo = sigmaOne * garsideDelta := by
  calc
    garsideDelta * sigmaTwo
        = (sigmaOne * sigmaTwo * sigmaOne) * sigmaTwo := by rfl
    _ = sigmaOne * (sigmaTwo * sigmaOne * sigmaTwo) := by
      simp only [mul_assoc]
    _ = sigmaOne * (sigmaOne * sigmaTwo * sigmaOne) := by
      rw [← artin_relation]
    _ = sigmaOne * garsideDelta := by rfl

/-- The square of the B₃ Garside element commutes with σ₁. -/
theorem b3_garside_sq_comm_sigmaOne :
    garsideDelta ^ 2 * sigmaOne = sigmaOne * garsideDelta ^ 2 := by
  calc
    garsideDelta ^ 2 * sigmaOne
        = garsideDelta * (garsideDelta * sigmaOne) := by
          simp [pow_two, mul_assoc]
    _ = garsideDelta * (sigmaTwo * garsideDelta) := by
          rw [b3_garside_mul_sigmaOne]
    _ = (garsideDelta * sigmaTwo) * garsideDelta := by
          simp only [mul_assoc]
    _ = (sigmaOne * garsideDelta) * garsideDelta := by
          rw [b3_garside_mul_sigmaTwo]
    _ = sigmaOne * garsideDelta ^ 2 := by
          simp [pow_two, mul_assoc]

/-- The square of the B₃ Garside element commutes with σ₂. -/
theorem b3_garside_sq_comm_sigmaTwo :
    garsideDelta ^ 2 * sigmaTwo = sigmaTwo * garsideDelta ^ 2 := by
  calc
    garsideDelta ^ 2 * sigmaTwo
        = garsideDelta * (garsideDelta * sigmaTwo) := by
          simp [pow_two, mul_assoc]
    _ = garsideDelta * (sigmaOne * garsideDelta) := by
          rw [b3_garside_mul_sigmaTwo]
    _ = (garsideDelta * sigmaOne) * garsideDelta := by
          simp only [mul_assoc]
    _ = (sigmaTwo * garsideDelta) * garsideDelta := by
          rw [b3_garside_mul_sigmaOne]
    _ = sigmaTwo * garsideDelta ^ 2 := by
          simp [pow_two, mul_assoc]

/-- Elements commuting with a fixed group element form a subgroup. -/
def commutantSubgroup {G : Type*} [Group G] (z : G) : Subgroup G where
  carrier := {g | z * g = g * z}
  one_mem' := by simp
  mul_mem' := by
    intro x y hx hy
    calc
      z * (x * y) = (z * x) * y := by simp only [mul_assoc]
      _ = (x * z) * y := by rw [hx]
      _ = x * (z * y) := by simp only [mul_assoc]
      _ = x * (y * z) := by rw [hy]
      _ = (x * y) * z := by simp only [mul_assoc]
  inv_mem' := by
    intro x hx
    apply (mul_right_cancel₀ x)
    calc
      (z * x⁻¹) * x = z := by simp [mul_assoc]
      _ = x⁻¹ * (x * z) := by simp
      _ = x⁻¹ * (z * x) := by rw [hx]
      _ = (x⁻¹ * z) * x := by simp only [mul_assoc]

/-- The square of the B₃ Garside element commutes with every braid. -/
theorem b3_garside_sq_central (g : BraidGroup3) :
    garsideDelta ^ 2 * g = g * garsideDelta ^ 2 := by
  let H : Subgroup BraidGroup3 := commutantSubgroup (garsideDelta ^ 2)
  have hgen : ∀ j : Generator, PresentedGroup.of j ∈ H := by
    intro j
    cases j
    · exact b3_garside_sq_comm_sigmaOne
    · exact b3_garside_sq_comm_sigmaTwo
  exact PresentedGroup.generated_by relations H hgen g

/-- The B₃ full twist is a pure braid: its permutation image is trivial. -/
theorem b3_garside_sq_mem_permutation_kernel :
    garsideDelta ^ 2 ∈ braidGroup3ToS3.ker := by
  change braidGroup3ToS3 (garsideDelta ^ 2) = 1
  rw [map_pow, garsideDelta_maps_to_outer_swap]
  apply Equiv.ext
  intro i
  fin_cases i <;> rfl

/-! ## I₂(6) = G₂ Artin group: even Coxeter length, Δ itself is central -/

namespace G2

open InfoGeometry.Exceptional.G2ArtinPresentation

/-- For I₂(6), the length-six Garside element commutes with the first generator. -/
theorem garside_comm_sigmaZero :
    garside * sigmaZero = sigmaZero * garside := by
  calc
    garside * sigmaZero =
        (sigmaZero * sigmaOne * sigmaZero * sigmaOne * sigmaZero * sigmaOne) *
          sigmaZero := by rfl
    _ = sigmaZero *
        (sigmaOne * sigmaZero * sigmaOne * sigmaZero * sigmaOne * sigmaZero) := by
      simp only [mul_assoc]
    _ = sigmaZero * garside := by
      rw [garside_eq_reverse]

/-- For I₂(6), the length-six Garside element commutes with the second generator. -/
theorem garside_comm_sigmaOne :
    garside * sigmaOne = sigmaOne * garside := by
  calc
    garside * sigmaOne =
        (sigmaOne * sigmaZero * sigmaOne * sigmaZero * sigmaOne * sigmaZero) *
          sigmaOne := by
      rw [garside_eq_reverse]
    _ = sigmaOne *
        (sigmaZero * sigmaOne * sigmaZero * sigmaOne * sigmaZero * sigmaOne) := by
      simp only [mul_assoc]
    _ = sigmaOne * garside := by rfl

/-- The G₂/I₂(6) Garside element commutes with every Artin-group element. -/
theorem garside_central (g : ArtinG2) :
    garside * g = g * garside := by
  let H : Subgroup ArtinG2 :=
    InfoGeometry.Categorical.ArtinGarsideCenterBridge.commutantSubgroup garside
  have hgen : ∀ j : Generator, PresentedGroup.of j ∈ H := by
    intro j
    fin_cases j
    · exact garside_comm_sigmaZero
    · exact garside_comm_sigmaOne
  exact PresentedGroup.generated_by relations H hgen g

/-- Consequently Δ² also commutes with every element, although Δ already does. -/
theorem garside_sq_central (g : ArtinG2) :
    garside ^ 2 * g = g * garside ^ 2 := by
  calc
    garside ^ 2 * g = garside * (garside * g) := by simp [pow_two, mul_assoc]
    _ = garside * (g * garside) := by rw [garside_central]
    _ = (garside * g) * garside := by simp only [mul_assoc]
    _ = (g * garside) * garside := by rw [garside_central]
    _ = g * garside ^ 2 := by simp [pow_two, mul_assoc]

end G2

/-! ## Pure-braid unipotent square identity -/

section NilpotentShear

variable {A : Type*} [Ring A]

/-- If N² = 0, then the square of the unipotent element 1+N is exactly 1+2N. -/
theorem one_add_nilpotent_sq
    (N : A) (hN : N * N = 0) :
    (1 + N) * (1 + N) = 1 + (2 : ℤ) • N := by
  calc
    (1 + N) * (1 + N)
        = 1 + N + N + N * N := by noncomm_ring
    _ = 1 + N + N := by rw [hN, add_zero]
    _ = 1 + (2 : ℤ) • N := by simp [two_zsmul]

end NilpotentShear

end InfoGeometry.Categorical.ArtinGarsideCenterBridge
