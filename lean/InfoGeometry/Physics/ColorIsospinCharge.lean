/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import InfoGeometry.Physics.ColorOccupationPolynomials
import Mathlib.Tactic.NoncommRing

/-!
# Ordered color-isospin charge table

The right-hand side is a polynomial expansion of a scaled charge expression.
It becomes an eigenvalue/spectral decomposition only after the sector terms
are proved to be mutually orthogonal idempotents on a specified module.
-/
namespace InfoGeometry.Physics.ColorIsospinCharge

open ColorOccupationPolynomials

variable {A : Type*} [Ring A]

def isoPlus (u v : A) : A := u * (1 - v)
def isoMinus (u v : A) : A := (1 - u) * v
def isoPair (u v : A) : A := u * v + (1 - u) * (1 - v)

theorem iso_partition (u v : A) :
    isoPlus u v + isoMinus u v + isoPair u v = 1 := by
  simp only [isoPlus, isoMinus, isoPair]
  noncomm_ring

/-- The scalar-free polynomial six-times-charge convention of the source note. -/
def charge6 (a b c u v : A) : A :=
  number a b c + (3 : ℕ) • (isoPlus u v - isoMinus u v)

/-- Exact ordered multiplet expansion, with no claim that the summands are
    spectral projections in an arbitrary ring. -/
theorem charge6_expansion (a b c u v : A) :
    charge6 a b c u v =
      (4 : ℕ) • (quark a b c * isoPlus u v) -
      (2 : ℕ) • (quark a b c * isoMinus u v) +
      quark a b c * isoPair u v +
      (5 : ℕ) • (diquark a b c * isoPlus u v) -
      diquark a b c * isoMinus u v +
      (2 : ℕ) • (diquark a b c * isoPair u v) +
      (6 : ℕ) • (baryon a b c * isoPlus u v) +
      (3 : ℕ) • (baryon a b c * isoPair u v) +
      (3 : ℕ) • (vacuum a b c * isoPlus u v) -
      (3 : ℕ) • (vacuum a b c * isoMinus u v) := by
  have h4 : ∀ x : A, (4 : ℕ) • x = x + x + x + x := fun x => by
    rw [show (4 : ℕ) = 2 + 2 from rfl, add_nsmul, two_nsmul]; abel
  have h5 : ∀ x : A, (5 : ℕ) • x = x + x + x + x + x := fun x => by
    rw [show (5 : ℕ) = 3 + 2 from rfl, add_nsmul, three_nsmul, two_nsmul]; abel
  have h6 : ∀ x : A, (6 : ℕ) • x = x + x + x + x + x + x := fun x => by
    rw [show (6 : ℕ) = 3 + 3 from rfl, add_nsmul, three_nsmul]; abel
  simp only [charge6, number, quark, diquark, baryon, vacuum,
    isoPlus, isoMinus, isoPair, two_nsmul, three_nsmul, h4, h5, h6]
  noncomm_ring

end InfoGeometry.Physics.ColorIsospinCharge
