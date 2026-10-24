/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Tactic.NoncommRing

/-!
# Ordered color occupation polynomials

The polynomial cancellations below hold in every associative ring, even when
the three occupation variables neither commute nor are idempotent. These are
identities of formal expressions, not spectral decompositions into genuine
orthogonal projections without further hypotheses.
-/

namespace InfoGeometry.Physics.ColorOccupationPolynomials

variable {A : Type*} [Ring A]

def baryon (a b c : A) : A := a * b * c
def vacuum (a b c : A) : A := (1 - a) * (1 - b) * (1 - c)
def quark (a b c : A) : A :=
  a * (1 - b) * (1 - c) +
  (1 - a) * b * (1 - c) +
  (1 - a) * (1 - b) * c

def diquark (a b c : A) : A :=
  (1 - a) * b * c +
  a * (1 - b) * c +
  a * b * (1 - c)

def number (a b c : A) : A := a + b + c
def t3 (a b : A) : A := a - b
def threeY (a b c : A) : A := a + b - (c + c)

/-- Noncommutative cancellation in the occupation-number polynomial. -/
theorem number_expansion (a b c : A) :
    number a b c = quark a b c + (2 : ℕ) • diquark a b c +
      (3 : ℕ) • baryon a b c := by
  simp only [number, quark, diquark, baryon, two_nsmul, three_nsmul]
  noncomm_ring

/-- The ordered quark and diquark expressions have a quadratic sum. -/
theorem colored_sum (a b c : A) :
    quark a b c + diquark a b c =
      a + b + c - a * b - a * c - b * c := by
  simp only [quark, diquark]
  noncomm_ring

/-- A formal four-sector partition, with products kept in a fixed order. -/
theorem sector_sum (a b c : A) :
    vacuum a b c + quark a b c + diquark a b c + baryon a b c = 1 := by
  simp only [vacuum, quark, diquark, baryon]
  noncomm_ring

/-- Symmetrized ordered Cartan polynomial identity, without an eigenvalue claim. -/
theorem cartan_polynomial (a b c : A) :
    (3 : ℕ) • (t3 a b * t3 a b) + threeY a b c * threeY a b c =
      (2 : ℕ) • ((quark a b c + diquark a b c) +
        (quark c b a + diquark c b a)) +
      (4 : ℕ) • ((a * a - a) + (b * b - b) + (c * c - c)) := by
  simp only [t3, threeY, quark, diquark,
    two_nsmul, three_nsmul, four_nsmul]
  noncomm_ring

end InfoGeometry.Physics.ColorOccupationPolynomials
