/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Algebra.AkivisIdentity

/-!
# Commutator derivations and Myung's criterion

We use Mathlib's `associator` and the repository's `akivisBracket` and
`akivisJacobiator`. The universal Leibniz identity is shared through
`Algebra.AkivisIdentity`; no associativity is assumed.

The necessity direction of Myung's criterion holds in every
`NonUnitalNonAssocRing`, including characteristic two. Its converse is stated
with precisely the cancellation assumption used by the proof: multiplication
by two on the additive group has trivial kernel. The ordinary flexibility
law and its polarized outer-skew consequence are kept distinct.

The alternative-algebra coefficient identities use integer scalar
multiplication and impose no characteristic restriction. Nonvanishing of
their right sides requires separate hypotheses.
-/

namespace InfoGeometry.Algebra

variable {A : Type*} [NonUnitalNonAssocRing A]

/-- Failure of the left commutator with `z` to obey the product rule on `x,y`. -/
def commutatorLeibnizDefect (x y z : A) : A :=
  akivisBracket z (x * y) - x * akivisBracket z y - akivisBracket z x * y

/-- The existing universal identity, in the argument order used by Myung. -/
theorem commutatorLeibnizDefect_eq_associators (x y z : A) :
    commutatorLeibnizDefect x y z =
      _root_.associator x z y - _root_.associator z x y -
        _root_.associator x y z := by
  exact akivisBracket_leibniz_defect_eq_associators x y z

theorem commutatorLeibnizDefect_eq_zero_iff (x y z : A) :
    commutatorLeibnizDefect x y z = 0 ↔
      akivisBracket z (x * y) = x * akivisBracket z y + akivisBracket z x * y := by
  unfold commutatorLeibnizDefect
  rw [sub_sub, sub_eq_zero]

/-- Jacobi is the difference of the product-rule defects in the two orders. -/
theorem akivisJacobiator_eq_commutatorLeibnizDefect_sub (x y z : A) :
    akivisJacobiator x y z =
      commutatorLeibnizDefect y x z - commutatorLeibnizDefect x y z := by
  rw [akivis_identity, commutatorLeibnizDefect_eq_associators,
    commutatorLeibnizDefect_eq_associators]
  abel

/-- Myung necessity: the unpolarized flexibility law needs no division by two. -/
theorem commutator_leibniz_implies_flexible
    (hLeib : ∀ x y z : A,
      akivisBracket z (x * y) = x * akivisBracket z y + akivisBracket z x * y)
    (x y : A) : _root_.associator x y x = 0 := by
  have hz := (commutatorLeibnizDefect_eq_zero_iff x y x).2 (hLeib x y x)
  rw [commutatorLeibnizDefect_eq_associators, sub_self, zero_sub] at hz
  exact neg_eq_zero.mp hz

/-- The outer-skew (linearized flexible) identity also follows in every characteristic. -/
theorem commutator_leibniz_implies_outer_skew
    (hLeib : ∀ x y z : A,
      akivisBracket z (x * y) = x * akivisBracket z y + akivisBracket z x * y)
    (x y z : A) : _root_.associator x y z = -_root_.associator z y x := by
  apply eq_neg_of_add_eq_zero_left
  calc
    _root_.associator x y z + _root_.associator z y x =
        -(commutatorLeibnizDefect x y z + commutatorLeibnizDefect z y x) := by
      rw [commutatorLeibnizDefect_eq_associators,
        commutatorLeibnizDefect_eq_associators]
      abel
    _ = 0 := by
      rw [(commutatorLeibnizDefect_eq_zero_iff x y z).2 (hLeib x y z),
        (commutatorLeibnizDefect_eq_zero_iff z y x).2 (hLeib z y x)]
      simp

/-- Myung necessity: the commutator satisfies Jacobi in every characteristic. -/
theorem commutator_leibniz_implies_jacobi
    (hLeib : ∀ x y z : A,
      akivisBracket z (x * y) = x * akivisBracket z y + akivisBracket z x * y)
    (x y z : A) : akivisJacobiator x y z = 0 := by
  rw [akivisJacobiator_eq_commutatorLeibnizDefect_sub,
    (commutatorLeibnizDefect_eq_zero_iff y x z).2 (hLeib y x z),
    (commutatorLeibnizDefect_eq_zero_iff x y z).2 (hLeib x y z), sub_self]

/-- The exact coefficient obstruction to the converse of Myung's criterion. -/
theorem two_smul_commutatorLeibnizDefect_eq_neg_jacobiator
    (hFlex : ∀ x y z : A,
      _root_.associator x y z = -_root_.associator z y x)
    (x y z : A) :
    (2 : ℤ) • commutatorLeibnizDefect x y z = -akivisJacobiator x y z := by
  rw [commutatorLeibnizDefect_eq_associators, akivis_identity,
    hFlex y z x, hFlex y x z, hFlex z y x]
  abel

/-- Converse of Myung's criterion under explicit cancellation of additive two-torsion. -/
theorem flexible_jacobi_implies_commutator_leibniz
    (hTwo : ∀ a : A, (2 : ℤ) • a = 0 → a = 0)
    (hFlex : ∀ x y z : A,
      _root_.associator x y z = -_root_.associator z y x)
    (hJac : ∀ x y z : A, akivisJacobiator x y z = 0)
    (x y z : A) :
    akivisBracket z (x * y) = x * akivisBracket z y + akivisBracket z x * y := by
  apply (commutatorLeibnizDefect_eq_zero_iff x y z).1
  apply hTwo
  rw [two_smul_commutatorLeibnizDefect_eq_neg_jacobiator hFlex, hJac, neg_zero]

/-- Exact Myung equivalence for additive groups without two-torsion. -/
theorem myung_iff_of_two_torsion_free
    (hTwo : ∀ a : A, (2 : ℤ) • a = 0 → a = 0) :
    (∀ x y z : A,
      akivisBracket z (x * y) = x * akivisBracket z y + akivisBracket z x * y) ↔
      (∀ x y z : A, _root_.associator x y z = -_root_.associator z y x) ∧
        (∀ x y z : A, akivisJacobiator x y z = 0) := by
  constructor
  · intro hLeib
    exact ⟨commutator_leibniz_implies_outer_skew hLeib,
      commutator_leibniz_implies_jacobi hLeib⟩
  · rintro ⟨hFlex, hJac⟩
    exact flexible_jacobi_implies_commutator_leibniz hTwo hFlex hJac

/-- In any ring with alternating associator, the product-rule defect is `-3 A(x,y,z)`.
This coefficient identity is valid even when three vanishes in the coefficient ring. -/
theorem commutatorLeibnizDefect_eq_neg_three_zsmul_associator
    (hAlt12 : ∀ x y z : A,
      _root_.associator x y z = -_root_.associator y x z)
    (hAlt23 : ∀ x y z : A,
      _root_.associator x y z = -_root_.associator x z y)
    (x y z : A) :
    commutatorLeibnizDefect x y z = (-3 : ℤ) • _root_.associator x y z := by
  have hxzy := hAlt23 x z y
  have hzxy : _root_.associator z x y = _root_.associator x y z := by
    rw [hAlt12 z x y, hAlt23 x z y, neg_neg]
  rw [commutatorLeibnizDefect_eq_associators, hxzy, hzxy]
  abel

/-- The characteristic-free integer form of the alternative Jacobi obstruction.
The existing real-scalar version is `alternative_akivisJacobiator_eq_six_smul_associator`. -/
theorem akivisJacobiator_eq_six_zsmul_associator
    (hAlt12 : ∀ x y z : A,
      _root_.associator x y z = -_root_.associator y x z)
    (hAlt23 : ∀ x y z : A,
      _root_.associator x y z = -_root_.associator x z y)
    (x y z : A) :
    akivisJacobiator x y z = (6 : ℤ) • _root_.associator x y z := by
  rw [akivisJacobiator_eq_commutatorLeibnizDefect_sub,
    commutatorLeibnizDefect_eq_neg_three_zsmul_associator hAlt12 hAlt23,
    commutatorLeibnizDefect_eq_neg_three_zsmul_associator hAlt12 hAlt23,
    hAlt12 y x z]
  abel

end InfoGeometry.Algebra
