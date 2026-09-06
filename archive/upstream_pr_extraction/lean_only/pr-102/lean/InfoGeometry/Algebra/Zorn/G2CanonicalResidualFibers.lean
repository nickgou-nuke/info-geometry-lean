/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords

/-!
# Boolean residual fibers over canonical `G₂` inversion sets

This is the coordinate side of a Bruhat residual fiber.  It intentionally
does not identify the fiber with a concrete subgroup until ordered root
products and their injectivity have been proved.
-/

namespace InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers

open InfoGeometry.Algebra.Zorn.G2CanonicalWeylWords
open InfoGeometry.Algebra.Zorn.G2Combinatorics

abbrev CanonicalResidualExponent (w : G2WeylElement) :=
  { α : G2PositiveRoot // α ∈ canonicalSignedInversionRoots w } → Bool

theorem canonicalSignedInversionRoots_id :
    canonicalSignedInversionRoots G2WeylElement.id = ∅ := by
  decide

theorem canonicalSignedInversionRoots_w0 :
    canonicalSignedInversionRoots G2WeylElement.w0 = Finset.univ := by
  decide

theorem canonicalResidualExponent_card (w : G2WeylElement) :
    Fintype.card (CanonicalResidualExponent w) =
      2 ^ weylLength w := by
  classical
  simp [CanonicalResidualExponent, canonicalSignedInversionRoots_card w]

noncomputable def canonicalResidualRootIndexEquiv (w : G2WeylElement) :
    { α : G2PositiveRoot // α ∈ canonicalSignedInversionRoots w } ≃
      Fin (weylLength w) :=
  Finite.equivFinOfCardEq (by
    simp [Nat.card_eq_fintype_card, canonicalSignedInversionRoots_card w])

noncomputable def canonicalResidualBinaryEquiv (w : G2WeylElement) :
    CanonicalResidualExponent w ≃ (Fin (weylLength w) → Bool) :=
  (canonicalResidualRootIndexEquiv w).arrowCongr (Equiv.refl Bool)

theorem canonicalResidualBinaryEquiv_card (w : G2WeylElement) :
    Fintype.card (Fin (weylLength w) → Bool) =
      Fintype.card (CanonicalResidualExponent w) := by
  exact Fintype.card_congr (canonicalResidualBinaryEquiv w).symm

noncomputable def canonicalResidualFiberBinaryEquiv :
    (Σ w : G2WeylElement, CanonicalResidualExponent w) ≃
      (Σ w : G2WeylElement, Fin (weylLength w) → Bool) where
  toFun x := ⟨x.1, canonicalResidualBinaryEquiv x.1 x.2⟩
  invFun x := ⟨x.1, (canonicalResidualBinaryEquiv x.1).symm x.2⟩
  left_inv x := by
    cases x with
    | mk w e => simp
  right_inv x := by
    cases x with
    | mk w e => simp

theorem canonicalResidualFiber_total_card :
    Fintype.card (Σ w : G2WeylElement, CanonicalResidualExponent w) = 189 := by
  calc
    Fintype.card (Σ w : G2WeylElement, CanonicalResidualExponent w) =
        ∑ w : G2WeylElement, Fintype.card (CanonicalResidualExponent w) :=
      Fintype.card_sigma
    _ = ∑ w : G2WeylElement, 2 ^ weylLength w := by
      apply Finset.sum_congr rfl
      intro w hw
      exact canonicalResidualExponent_card w
    _ = poincarePolynomial 2 := rfl
    _ = 189 := poincare_polynomial_at_two

theorem canonicalResidualFiberBinaryEquiv_card :
    Fintype.card (Σ w : G2WeylElement, Fin (weylLength w) → Bool) = 189 := by
  exact (Fintype.card_congr canonicalResidualFiberBinaryEquiv).trans
    canonicalResidualFiber_total_card

noncomputable def canonicalFlagIndexEquiv :
    (Σ w : G2WeylElement, CanonicalResidualExponent w) ≃ Fin 189 :=
  Finite.equivFinOfCardEq (by
    rw [Nat.card_eq_fintype_card]
    exact canonicalResidualFiber_total_card)

noncomputable def canonicalBinaryFlagIndexEquiv :
    (Σ w : G2WeylElement, Fin (weylLength w) → Bool) ≃ Fin 189 :=
  canonicalResidualFiberBinaryEquiv.symm.trans canonicalFlagIndexEquiv

end InfoGeometry.Algebra.Zorn.G2CanonicalResidualFibers
