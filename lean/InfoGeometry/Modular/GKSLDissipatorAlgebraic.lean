import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Star.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Algebraic Foundations of the GKSL / Lindblad Dissipator

This module formalizes the exact algebraic structure of the Gorini–Kossakowski–Sudarshan–Lindblad
(GKSL) open quantum dynamical generator:
  𝒟(X) = ∑_k ( V_k† X V_k - (1/2) {V_k† V_k, X} )

Proven theorems:
1. Identity / Vacuum Annihilation: 𝒟(1) = 0.
2. Self-Adjointness Preservation: X = X† ⟹ 𝒟(X) = 𝒟(X)†.
3. Full Lindbladian Unitality: ℒ(1) = [H, 1] + 𝒟(1) = 0.

All proofs are complete in native Mathlib with zero `sorry`s and zero custom axioms.
-/

noncomputable section

open BigOperators
open Finset

namespace InfoGeometry.Modular.GKSL

variable {A : Type*} [Ring A] [StarRing A]

/-!
=============================================================================
PART 1: The Single-Channel GKSL Dissipator Term
=============================================================================
-/

/-- 
  A single Lindblad jump channel dissipator term:
  𝒟_V(X) = V† X V - (1/2) * (V† V X + X V† V)
-/
def dissipatorTerm (half : A) (V_k : A) (X : A) : A :=
  star V_k * X * V_k - half * (star V_k * V_k * X + X * star V_k * V_k)

/-- 
  THEOREM 1: The Dissipator Term Strictly Annihilates the Identity Element:
  𝒟_V(1) = 0
  This is the algebraic generator of quantum probability / trace preservation.
-/
theorem dissipatorTerm_one
    (half : A) (h_half : (2 : A) * half = 1) (h_half_comm : ∀ x : A, half * x = x * half)
    (V_k : A) :
    dissipatorTerm half V_k 1 = 0 := by
  dsimp [dissipatorTerm]
  simp only [mul_one, one_mul]
  have h_two : star V_k * V_k + star V_k * V_k = (2 : A) * (star V_k * V_k) := by
    rw [two_mul]
  rw [h_two]
  have h_cancel : half * ((2 : A) * (star V_k * V_k)) = star V_k * V_k := by
    calc
      half * ((2 : A) * (star V_k * V_k)) = (half * (2 : A)) * (star V_k * V_k) := (mul_assoc _ _ _).symm
      _ = ((2 : A) * half) * (star V_k * V_k) := by rw [h_half_comm]
      _ = 1 * (star V_k * V_k) := by rw [h_half]
      _ = star V_k * V_k := one_mul _
  rw [h_cancel, sub_self]

/-- 
  THEOREM 2 (Star-Covariance of the Dissipator Term):
  (𝒟_V(X))† = 𝒟_V(X†)
-/
theorem dissipatorTerm_star
    (half : A) (h_half_comm : ∀ x : A, half * x = x * half) (h_half_star : star half = half)
    (V_k : A) (X : A) :
    star (dissipatorTerm half V_k X) = dissipatorTerm half V_k (star X) := by
  dsimp [dissipatorTerm]
  simp only [star_sub, star_mul, star_add, star_star, h_half_star]
  have h_comm1 : (star X * (star V_k * V_k) + star V_k * (V_k * star X)) * half =
      half * (star V_k * V_k * star X + star X * star V_k * V_k) := by
    rw [h_half_comm]
    simp only [mul_assoc]
    abel
  rw [h_comm1]
  simp only [mul_assoc]

/-!
=============================================================================
PART 2: Full Multichannel GKSL Dissipator and Lindbladian
=============================================================================
-/

variable {ι : Type*} [Fintype ι]

/-- The Multichannel GKSL Dissipator: 𝒟(X) = ∑_k 𝒟_{V_k}(X). -/
def gkslDissipator (half : A) (V : ι → A) (X : A) : A :=
  ∑ k, dissipatorTerm half (V k) X

/-- 
  THEOREM 3: The Full GKSL Dissipator Annihilates the Identity Element:
  𝒟(1) = 0
-/
@[simp]
theorem gkslDissipator_one
    (half : A) (h_half : (2 : A) * half = 1) (h_half_comm : ∀ x : A, half * x = x * half)
    (V : ι → A) :
    gkslDissipator half V 1 = 0 := by
  dsimp [gkslDissipator]
  have h_zeros : ∀ k ∈ (Finset.univ : Finset ι), dissipatorTerm half (V k) 1 = 0 := by
    intro k _
    exact dissipatorTerm_one half h_half h_half_comm (V k)
  rw [Finset.sum_congr rfl h_zeros, Finset.sum_const_zero]

/-- 
  THEOREM 4: The Full GKSL Dissipator Preserves Self-Adjoint Observables:
  X = X† ⟹ 𝒟(X) = 𝒟(X)†
-/
theorem gkslDissipator_self_adjoint
    (half : A) (h_half_comm : ∀ x : A, half * x = x * half) (h_half_star : star half = half)
    (V : ι → A) (X : A) (hX : star X = X) :
    star (gkslDissipator half V X) = gkslDissipator half V X := by
  dsimp [gkslDissipator]
  rw [star_sum]
  have h_terms : ∀ k ∈ (Finset.univ : Finset ι),
      star (dissipatorTerm half (V k) X) = dissipatorTerm half (V k) X := by
    intro k _
    rw [dissipatorTerm_star half h_half_comm h_half_star (V k) X, hX]
  exact Finset.sum_congr rfl h_terms

/-- 
  The Total Lindblad Generator of Open Quantum Dynamics:
  ℒ(X) = [H, X] + 𝒟(X)
-/
def totalLindbladian (half : A) (H : A) (V : ι → A) (X : A) : A :=
  (H * X - X * H) + gkslDissipator half V X

/-- 
  THEOREM 5: The Full Lindbladian is Unital (Identity-Preserving):
  ℒ(1) = 0
-/
@[simp]
theorem totalLindbladian_one
    (half : A) (h_half : (2 : A) * half = 1) (h_half_comm : ∀ x : A, half * x = x * half)
    (H : A) (V : ι → A) :
    totalLindbladian half H V 1 = 0 := by
  dsimp [totalLindbladian]
  simp only [mul_one, one_mul, sub_self, zero_add]
  exact gkslDissipator_one half h_half h_half_comm V

end InfoGeometry.Modular.GKSL

end noncomputable section
