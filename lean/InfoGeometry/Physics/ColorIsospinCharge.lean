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
  have hc := sector_sum a b c
  have hn := number_expansion a b c
  have hi := iso_partition u v
  unfold charge6
  rw [hn]
  calc
    quark a b c + (2 : ℕ) • diquark a b c +
        (3 : ℕ) • baryon a b c +
        (3 : ℕ) • (isoPlus u v - isoMinus u v) =
      (quark a b c + (2 : ℕ) • diquark a b c +
        (3 : ℕ) • baryon a b c) *
        (isoPlus u v + isoMinus u v + isoPair u v) +
      (3 : ℕ) • (vacuum a b c + quark a b c +
        diquark a b c + baryon a b c) *
        (isoPlus u v - isoMinus u v) := by
          rw [hi, hc, mul_one, one_mul]
    _ = _ := by
      simp only [two_nsmul, three_nsmul, four_nsmul,
        five_nsmul, six_nsmul]
      noncomm_ring

end InfoGeometry.Physics.ColorIsospinCharge
