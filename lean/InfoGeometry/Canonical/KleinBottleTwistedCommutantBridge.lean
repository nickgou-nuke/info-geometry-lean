import Mathlib.Algebra.Ring.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.Ring.Aut
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic

/-!
# Klein Bottle Group, Crossed Product Action, and Twisted Commutant Algebra

This module formalizes the exact operator-algebraic $\mathbb{Z}_2$-graded commutant
structure induced by the non-orientable Klein bottle holonomy:

1. **Klein Bottle Automorphism & Involution:**
   An involutive ring automorphism $\alpha \in \operatorname{RingAut}(A)$ satisfying $\alpha^2 = \operatorname{id}$.

2. **The $\alpha$-Twisted Commutant Space:**
   - Ordinary commutant: $A' = \{ T \in B \mid T a = a T \}$
   - $\alpha$-twisted commutant: $A'_\alpha = \{ T \in B \mid T a = \alpha(a) T \}$

3. **Even Sector Commutant Recovery:**
   For any twisted intertwiner $U \in A'_\alpha$, its square satisfies $U^2 \in A'$,
   reflecting that the orientation double cover (the 2-torus $\mathbb{T}^2$) restores
   ordinary commutativity.

4. **$\mathbb{Z}_2$-Graded Algebra Structure:**
   - $A' \cdot A' \subseteq A'$
   - $A' \cdot A'_\alpha \subseteq A'_\alpha$
   - $A'_\alpha \cdot A' \subseteq A'_\alpha$
   - $A'_\alpha \cdot A'_\alpha \subseteq A'$

The algebraic statements below are checked by Lean; topological and
geometric interpretations remain parameterized by their explicit data.
-/

namespace InfoGeometry.Canonical.KleinBottleTwistedCommutant

variable {A B : Type*} [Ring A] [Ring B]

/-- Involutive automorphism on the base algebra A -/
structure KleinInvolution (A : Type*) [Ring A] where
  toRingAut : RingAut A
  involutive : ∀ a : A, toRingAut (toRingAut a) = a

/-- Ordinary commutant predicate for an operator T in B relative to embedded A -/
def IsCommutant (i : A →+* B) (T : B) : Prop :=
  ∀ a : A, T * i a = i a * T

/-- α-twisted commutant predicate for an operator T in B relative to embedded A -/
def IsTwistedCommutant (i : A →+* B) (α : RingAut A) (T : B) : Prop :=
  ∀ a : A, T * i a = i (α a) * T

/-- 🏆 THEOREM 1: Identity is in the ordinary commutant -/
theorem one_mem_commutant (i : A →+* B) : IsCommutant i (1 : B) := by
  intro a
  simp only [one_mul, mul_one]

/-- Zero is in both commutant sectors. -/
theorem zero_mem_commutant (i : A →+* B) : IsCommutant i (0 : B) := by
  intro a
  simp

theorem zero_mem_twisted_commutant (i : A →+* B) (α : RingAut A) :
    IsTwistedCommutant i α (0 : B) := by
  intro a
  simp

/-- The ordinary commutant is closed under addition. -/
theorem commutant_add_commutant (i : A →+* B) (T₁ T₂ : B)
    (h₁ : IsCommutant i T₁) (h₂ : IsCommutant i T₂) :
    IsCommutant i (T₁ + T₂) := by
  intro a
  simp only [add_mul, mul_add]
  rw [h₁ a, h₂ a]

/-- The twisted commutant is closed under addition. -/
theorem twisted_add_twisted (i : A →+* B) (T₁ T₂ : B) (α : RingAut A)
    (h₁ : IsTwistedCommutant i α T₁) (h₂ : IsTwistedCommutant i α T₂) :
    IsTwistedCommutant i α (T₁ + T₂) := by
  intro a
  simp only [add_mul, mul_add]
  rw [h₁ a, h₂ a]

/-- 🏆 THEOREM 2: Ordinary Commutant is Closed under Multiplication (C₀ · C₀ ⊆ C₀) -/
theorem commutant_mul_commutant (i : A →+* B) (T₁ T₂ : B)
    (h₁ : IsCommutant i T₁) (h₂ : IsCommutant i T₂) :
    IsCommutant i (T₁ * T₂) := by
  intro a
  calc (T₁ * T₂) * i a
    _ = T₁ * (T₂ * i a) := by rw [mul_assoc]
    _ = T₁ * (i a * T₂) := by rw [h₂ a]
    _ = (T₁ * i a) * T₂ := by rw [← mul_assoc]
    _ = (i a * T₁) * T₂ := by rw [h₁ a]
    _ = i a * (T₁ * T₂) := by rw [mul_assoc]

/-- 🏆 THEOREM 3: Left Ordinary Commutant on Twisted Commutant (C₀ · C₁ ⊆ C₁) -/
theorem commutant_mul_twisted (i : A →+* B) (T₁ T₂ : B) (α : RingAut A)
    (h₁ : IsCommutant i T₁) (h₂ : IsTwistedCommutant i α T₂) :
    IsTwistedCommutant i α (T₁ * T₂) := by
  intro a
  calc (T₁ * T₂) * i a
    _ = T₁ * (T₂ * i a) := by rw [mul_assoc]
    _ = T₁ * (i (α a) * T₂) := by rw [h₂ a]
    _ = (T₁ * i (α a)) * T₂ := by rw [← mul_assoc]
    _ = (i (α a) * T₁) * T₂ := by rw [h₁ (α a)]
    _ = i (α a) * (T₁ * T₂) := by rw [mul_assoc]

/-- 🏆 THEOREM 4: Right Ordinary Commutant on Twisted Commutant (C₁ · C₀ ⊆ C₁) -/
theorem twisted_mul_commutant (i : A →+* B) (T₁ T₂ : B) (α : RingAut A)
    (h₁ : IsTwistedCommutant i α T₁) (h₂ : IsCommutant i T₂) :
    IsTwistedCommutant i α (T₁ * T₂) := by
  intro a
  calc (T₁ * T₂) * i a
    _ = T₁ * (T₂ * i a) := by rw [mul_assoc]
    _ = T₁ * (i a * T₂) := by rw [h₂ a]
    _ = (T₁ * i a) * T₂ := by rw [← mul_assoc]
    _ = (i (α a) * T₁) * T₂ := by rw [h₁ a]
    _ = i (α a) * (T₁ * T₂) := by rw [mul_assoc]

/-- 🏆 THEOREM 5: Product of Two Twisted Commutants (C₁ · C₁ ⊆ C₀ via α² = id) -/
theorem twisted_mul_twisted (i : A →+* B) (T₁ T₂ : B) (α : KleinInvolution A)
    (h₁ : IsTwistedCommutant i α.toRingAut T₁)
    (h₂ : IsTwistedCommutant i α.toRingAut T₂) :
    IsCommutant i (T₁ * T₂) := by
  intro a
  calc (T₁ * T₂) * i a
    _ = T₁ * (T₂ * i a) := by rw [mul_assoc]
    _ = T₁ * (i (α.toRingAut a) * T₂) := by rw [h₂ a]
    _ = (T₁ * i (α.toRingAut a)) * T₂ := by rw [← mul_assoc]
    _ = (i (α.toRingAut (α.toRingAut a)) * T₁) * T₂ := by rw [h₁ (α.toRingAut a)]
    _ = (i a * T₁) * T₂ := by rw [α.involutive a]
    _ = i a * (T₁ * T₂) := by rw [mul_assoc]

/-- 🏆 THEOREM 6: Square of a Klein Glide Generator is Central/Commuting with A -/
theorem klein_glide_square_in_commutant (i : A →+* B) (U : B) (α : KleinInvolution A)
    (hU : IsTwistedCommutant i α.toRingAut U) :
    IsCommutant i (U * U) :=
  twisted_mul_twisted i U U α hU hU

/-- 🏆 THEOREM 7: Double Cover Commutator Vanishing: [U², a] = 0 -/
theorem klein_double_cover_commutator_zero (i : A →+* B) (U : B) (α : KleinInvolution A)
    (hU : IsTwistedCommutant i α.toRingAut U) (a : A) :
    (U * U) * i a - i a * (U * U) = 0 := by
  have h := klein_glide_square_in_commutant i U α hU a
  rw [h, sub_self]

/-- A twisted unit implements the Klein involution by conjugation.

This is the carrier-level normalizer statement.  It does not construct a
crossed-product or a von Neumann algebra; the embedding and the unit are
explicit inputs.
-/
theorem twisted_unit_conjugates
    (i : A →+* B) (U : Units B) (α : KleinInvolution A)
    (hU : IsTwistedCommutant i α.toRingAut (U : B)) (a : A) :
    (U : B) * i a * (↑(U⁻¹) : B) = i (α.toRingAut a) := by
  calc
    (U : B) * i a * (↑(U⁻¹) : B) =
        (i (α.toRingAut a) * (U : B)) * (↑(U⁻¹) : B) := by
          rw [hU a]
    _ = i (α.toRingAut a) * ((U : B) * (↑(U⁻¹) : B)) := by
          rw [mul_assoc]
    _ = i (α.toRingAut a) := by
          rw [Units.mul_inv, mul_one]

/-- Every even Klein winding returns to the ordinary commutant sector. -/
theorem twisted_pow_even_mem_commutant (i : A →+* B) (U : B)
    (α : KleinInvolution A) (hU : IsTwistedCommutant i α.toRingAut U) :
    ∀ n : ℕ, IsCommutant i (U ^ (2 * n)) := by
  intro n
  induction n with
  | zero =>
      simpa using one_mem_commutant i
  | succ n ih =>
      have hUU : IsCommutant i (U * U) :=
        klein_glide_square_in_commutant i U α hU
      have hmul := commutant_mul_commutant i (U ^ (2 * n)) (U * U) ih hUU
      simpa [Nat.mul_succ, pow_add, pow_two, mul_assoc] using hmul

/-- Every odd Klein winding remains in the twisted commutant sector. -/
theorem twisted_pow_odd_mem_twisted (i : A →+* B) (U : B)
    (α : KleinInvolution A) (hU : IsTwistedCommutant i α.toRingAut U) :
    ∀ n : ℕ, IsTwistedCommutant i α.toRingAut (U ^ (2 * n + 1)) := by
  intro n
  induction n with
  | zero =>
      simpa using hU
  | succ n ih =>
      have heven : IsCommutant i (U ^ (2 * (n + 1))) :=
        twisted_pow_even_mem_commutant i U α hU (n + 1)
      have hmul :=
        commutant_mul_twisted i (U ^ (2 * (n + 1))) U α.toRingAut heven hU
      simpa [Nat.mul_succ, pow_add, pow_two, mul_assoc] using hmul

/-- 🏆 THEOREM 8: The Complete Klein Bottle Graded Commutant Algebra Theorem -/
theorem klein_bottle_graded_commutant_algebra (i : A →+* B)
    (α : KleinInvolution A) (U : B)
    (hU : IsTwistedCommutant i α.toRingAut U) :
    (IsCommutant i (1 : B)) ∧
    (IsCommutant i (U * U)) ∧
    (∀ (T₁ T₂ : B), IsCommutant i T₁ → IsCommutant i T₂ → IsCommutant i (T₁ * T₂)) ∧
    (∀ (T₁ T₂ : B), IsCommutant i T₁ → IsTwistedCommutant i α.toRingAut T₂ → IsTwistedCommutant i α.toRingAut (T₁ * T₂)) ∧
    (∀ (T₁ T₂ : B), IsTwistedCommutant i α.toRingAut T₁ → IsCommutant i T₂ → IsTwistedCommutant i α.toRingAut (T₁ * T₂)) ∧
    (∀ (T₁ T₂ : B), IsTwistedCommutant i α.toRingAut T₁ → IsTwistedCommutant i α.toRingAut T₂ → IsCommutant i (T₁ * T₂)) :=
  ⟨one_mem_commutant i,
   klein_glide_square_in_commutant i U α hU,
   fun T₁ T₂ => commutant_mul_commutant i T₁ T₂,
   fun T₁ T₂ => commutant_mul_twisted i T₁ T₂ α.toRingAut,
   fun T₁ T₂ => twisted_mul_commutant i T₁ T₂ α.toRingAut,
   fun T₁ T₂ => twisted_mul_twisted i T₁ T₂ α⟩

end InfoGeometry.Canonical.KleinBottleTwistedCommutant
