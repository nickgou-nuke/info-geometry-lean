/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.PeirceDeWittChiralSplit
import InfoGeometry.Core.PeirceDecomposition
import InfoGeometry.OperatorAlgebra.InnerConjugation

/-!
# Parity closure for the native Peirce split

Adapted selectively from upstream/feat/cartan-drazin-mp-cycle,
commit 6a2dd21237e949f8fb8ffc75bf90e996e0cb65c2,
`Core/IdempotentCartan.lean`.

Contract: an associative ring A, the native `IsIdempotent p : p * p = p`,
and the existing `evenPart`, `oddPart`, `grading` of
`Algebra.PeirceDeWittChiralSplit`. No alternative corner or parity definitions.
The native four-corner owner remains `Algebra.IdempotentProjector`.
`Core.PeirceDecomposition.idempotent_mul_nested` supplies only a reusable
normalization lemma; `OperatorAlgebra.innerConjugationRingEquiv` supplies the
generic conjugation construction. Existing decomposition, grading square,
conjugation-on-parts, and odd-odd closure are reused, not reintroduced.

Projection, uniqueness, product, and commutator statements require no division
by two. Only the sign-eigenspace converses assume injective doubling. No star,
positivity, Cartan classification, nilpotent odd ideal, or continuum claim.
-/

namespace InfoGeometry.Algebra.PeirceDeWittChiralSplit

variable {A : Type*} [Ring A]

theorem evenPart_add (p x y : A) :
    evenPart p (x + y) = evenPart p x + evenPart p y := by
  unfold evenPart peirce11 peirce00
  simp only [mul_add, add_mul]
  abel

theorem oddPart_add (p x y : A) :
    oddPart p (x + y) = oddPart p x + oddPart p y := by
  unfold oddPart peirce10 peirce01
  simp only [mul_add, add_mul]
  abel

theorem evenPart_evenPart {p : A} (hp : IsIdempotent p) (x : A) :
    evenPart p (evenPart p x) = evenPart p x := by
  have hp' : p * p = p := hp
  simp only [evenPart, peirce11, peirce00, compIdempotent]
  noncomm_ring [hp', InfoGeometry.Core.PeirceDecomposition.idempotent_mul_nested p hp']

theorem evenPart_oddPart {p : A} (hp : IsIdempotent p) (x : A) :
    evenPart p (oddPart p x) = 0 := by
  have hp' : p * p = p := hp
  simp only [evenPart, oddPart, peirce11, peirce00, peirce10, peirce01,
    compIdempotent]
  noncomm_ring [hp', InfoGeometry.Core.PeirceDecomposition.idempotent_mul_nested p hp']

theorem oddPart_evenPart {p : A} (hp : IsIdempotent p) (x : A) :
    oddPart p (evenPart p x) = 0 := by
  have h := peirce_even_odd_decomposition p (evenPart p x)
  rw [evenPart_evenPart hp] at h
  have hz : (0 : A) = oddPart p (evenPart p x) := by
    apply add_left_cancel (a := evenPart p x)
    simpa only [add_zero] using h
  exact hz.symm

theorem oddPart_oddPart {p : A} (hp : IsIdempotent p) (x : A) :
    oddPart p (oddPart p x) = oddPart p x := by
  have h := peirce_even_odd_decomposition p (oddPart p x)
  rw [evenPart_oddPart hp, zero_add] at h
  exact h.symm

/-- Uniqueness uses the native projections, not sign eigenspaces. -/
theorem parity_decomposition_unique {p e o x : A} (hp : IsIdempotent p)
    (he : evenPart p e = e) (ho : oddPart p o = o) (hx : e + o = x) :
    e = evenPart p x ∧ o = oddPart p x := by
  have heo : evenPart p o = 0 := by
    rw [← ho]
    exact evenPart_oddPart hp o
  have hoe : oddPart p e = 0 := by
    rw [← he]
    exact oddPart_evenPart hp e
  rw [← hx, evenPart_add, oddPart_add, he, ho, heo, hoe, add_zero, zero_add]
  exact ⟨rfl, rfl⟩

/-- Diagonal product formula over an arbitrary ring. -/
theorem evenPart_mul {p : A} (hp : IsIdempotent p) (x y : A) :
    evenPart p (x * y) =
      evenPart p x * evenPart p y + oddPart p x * oddPart p y := by
  have hp' : p * p = p := hp
  simp only [evenPart, oddPart, peirce11, peirce00, peirce10, peirce01,
    compIdempotent]
  noncomm_ring [hp', InfoGeometry.Core.PeirceDecomposition.idempotent_mul_nested p hp']

/-- Off-diagonal product formula; neither input is required to be homogeneous. -/
theorem oddPart_mul {p : A} (hp : IsIdempotent p) (x y : A) :
    oddPart p (x * y) =
      evenPart p x * oddPart p y + oddPart p x * evenPart p y := by
  have hp' : p * p = p := hp
  simp only [evenPart, oddPart, peirce11, peirce00, peirce10, peirce01,
    compIdempotent]
  noncomm_ring [hp', InfoGeometry.Core.PeirceDecomposition.idempotent_mul_nested p hp']

/-- Specialize the existing inner automorphism to the native involutive grading. -/
def gradingConjugationEquiv (p : A) (hp : IsIdempotent p) : A ≃+* A :=
  InfoGeometry.OperatorAlgebra.innerConjugationRingEquiv
    { val := grading p
      inv := grading p
      val_inv := grading_sq p hp
      inv_val := grading_sq p hp }

theorem gradingConjugationEquiv_apply (p : A) (hp : IsIdempotent p) (x : A) :
    gradingConjugationEquiv p hp x = grading p * x * grading p := rfl

/-- The conjugation formula itself needs no idempotency premise. -/
theorem grading_conjugation_eq_even_sub_odd (p x : A) :
    grading p * x * grading p = evenPart p x - oddPart p x := by
  unfold grading evenPart oddPart peirce11 peirce00 peirce10 peirce01 compIdempotent
  noncomm_ring

theorem two_nsmul_evenPart (p x : A) :
    (2 : ℕ) • evenPart p x = x + grading p * x * grading p := by
  rw [grading_conjugation_eq_even_sub_odd, two_nsmul]
  calc
    evenPart p x + evenPart p x =
        (evenPart p x + oddPart p x) + (evenPart p x - oddPart p x) := by abel
    _ = x + (evenPart p x - oddPart p x) := by
      rw [← peirce_even_odd_decomposition p x]

theorem two_nsmul_oddPart (p x : A) :
    (2 : ℕ) • oddPart p x = x - grading p * x * grading p := by
  rw [grading_conjugation_eq_even_sub_odd, two_nsmul]
  calc
    oddPart p x + oddPart p x =
        (evenPart p x + oddPart p x) - (evenPart p x - oddPart p x) := by abel
    _ = x - (evenPart p x - oddPart p x) := by
      rw [← peirce_even_odd_decomposition p x]

/-- Recovery of the odd projection from the ordinary commutator. -/
theorem oddPart_eq_grading_mul_commutator {p : A} (hp : IsIdempotent p) (x : A) :
    oddPart p x = grading p * (p * x - x * p) := by
  have hp' : p * p = p := hp
  unfold oddPart grading peirce10 peirce01 compIdempotent
  noncomm_ring [hp', InfoGeometry.Core.PeirceDecomposition.idempotent_mul_nested p hp']

theorem oddPart_eq_double_commutator {p : A} (hp : IsIdempotent p) (x : A) :
    oddPart p x = p * (p * x - x * p) - (p * x - x * p) * p := by
  have hp' : p * p = p := hp
  unfold oddPart peirce10 peirce01 compIdempotent
  noncomm_ring [hp', InfoGeometry.Core.PeirceDecomposition.idempotent_mul_nested p hp']

theorem grading_mul_oddPart {p : A} (hp : IsIdempotent p) (x : A) :
    grading p * oddPart p x = p * x - x * p := by
  rw [oddPart_eq_grading_mul_commutator hp, ← mul_assoc, grading_sq p hp, one_mul]

/-- Vanishing of the odd projection characterizes the centralizer of p,
including in characteristic two. -/
theorem oddPart_zero_iff_commute {p : A} (hp : IsIdempotent p) (x : A) :
    oddPart p x = 0 ↔ p * x = x * p := by
  constructor
  · intro hx
    have h := grading_mul_oddPart hp x
    rw [hx, mul_zero] at h
    exact sub_eq_zero.mp h.symm
  · intro hx
    rw [oddPart_eq_grading_mul_commutator hp, hx, sub_self, mul_zero]

/-- The positive sign converse requires injective doubling. -/
theorem evenPart_eq_self_iff_grading_conjugation {p : A} (hp : IsIdempotent p)
    (h2 : Function.Injective (fun z : A => (2 : ℕ) • z)) (x : A) :
    evenPart p x = x ↔ grading p * x * grading p = x := by
  constructor
  · intro hx
    simpa only [hx] using grading_conjugates_evenPart p hp x
  · intro hx
    apply h2
    dsimp only
    rw [two_nsmul_evenPart, hx, two_nsmul]

/-- The negative sign converse has the same explicit doubling hypothesis. -/
theorem oddPart_eq_self_iff_grading_conjugation {p : A} (hp : IsIdempotent p)
    (h2 : Function.Injective (fun z : A => (2 : ℕ) • z)) (x : A) :
    oddPart p x = x ↔ grading p * x * grading p = -x := by
  constructor
  · intro hx
    simpa only [hx] using grading_conjugates_oddPart p hp x
  · intro hx
    apply h2
    dsimp only
    rw [two_nsmul_oddPart, hx, sub_neg_eq_add, two_nsmul]

end InfoGeometry.Algebra.PeirceDeWittChiralSplit
