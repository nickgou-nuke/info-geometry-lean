/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Basic.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Arithmetic and split-quadratic statements from the holographic white paper

Source: *Complete Holographic White Paper*, version 6.1, sections 2.4 and 5.6.1.
The residue condition is necessary for primes larger than three; its converse is
false. The intersection of the two displayed quadrics is an entire circle.
Neither statement constructs a continuous gauge group or a physical spacetime.

The Chinese-remainder construction is Mathlib's existing ring equivalence. The
repository already uses it in `Canonical/FiniteHeisenbergCRT`; the results here
only compute its images of the two residue classes relevant to this source.
-/

namespace InfoGeometry.Holographic.ArithmeticGeometry

/-- A prime larger than three lies in one of the two unit residue classes modulo six. -/
theorem prime_mod_six {p : ℕ} (hp : p.Prime) (hlarge : 3 < p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have hp2 : p ≠ 2 := ne_of_gt (lt_trans (by decide : 2 < 3) hlarge)
  have htwo : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  have hthree : p % 3 ≠ 0 := by
    intro h
    have heq : p = 3 := (hp.dvd_iff_eq (by decide : (3 : ℕ) ≠ 1)).mp
      (Nat.dvd_of_mod_eq_zero h)
    exact (ne_of_gt hlarge) heq
  omega

/-- For twin primes beyond the exceptional pair `(3, 5)`, the smaller prime is `5 mod 6`. -/
theorem twin_prime_mod_six {p : ℕ} (hp : p.Prime) (hnext : (p + 2).Prime)
    (hlarge : 3 < p) : p % 6 = 5 ∧ (p + 2) % 6 = 1 := by
  have hpmod := prime_mod_six hp hlarge
  have hnextmod := prime_mod_six hnext (by omega)
  omega

/-- The two residue classes also contain composite numbers. -/
theorem composite_residue_witnesses :
    25 % 6 = 1 ∧ ¬Nat.Prime 25 ∧ 35 % 6 = 5 ∧ ¬Nat.Prime 35 := by
  decide

/-- Modulus three already restricts primes to two possible nonzero residue classes. -/
theorem prime_mod_three {p : ℕ} (hp : p.Prime) (hlarge : 3 < p) :
    p % 3 = 1 ∨ p % 3 = 2 := by
  have h := prime_mod_six hp hlarge
  omega

/-- Modulus four also gives two possible residue classes for primes beyond two. -/
theorem prime_mod_four {p : ℕ} (hp : p.Prime) (hlarge : 2 < p) :
    p % 4 = 1 ∨ p % 4 = 3 := by
  have h := hp.eq_two_or_odd.resolve_left (ne_of_gt hlarge)
  omega

/-- Under the native CRT equivalence, residue one maps to `(1, 1)`. -/
theorem crt_one :
    ZMod.chineseRemainder (m := 2) (n := 3) (by decide) (1 : ZMod 6) =
      (1, 1) := by
  exact map_one _

/-- Under the native CRT equivalence, residue five maps to `(1, 2)`. -/
theorem crt_five :
    ZMod.chineseRemainder (m := 2) (n := 3) (by decide) (5 : ZMod 6) =
      (1, 2) := by
  change ZMod.chineseRemainder (m := 2) (n := 3) (by decide)
    ((5 : ℕ) : ZMod 6) = (1, 2)
  rw [map_natCast]
  decide

/-- The split quadric and the Euclidean unit sphere intersect in a circle. -/
theorem split_quadric_inter_sphere_iff (x y u v : ℝ) :
    (x ^ 2 + y ^ 2 - u ^ 2 - v ^ 2 = 1 ∧
      x ^ 2 + y ^ 2 + u ^ 2 + v ^ 2 = 1) ↔
      u = 0 ∧ v = 0 ∧ x ^ 2 + y ^ 2 = 1 := by
  constructor
  · rintro ⟨hsplit, hsphere⟩
    have hu2 : u ^ 2 = 0 := by
      nlinarith [sq_nonneg u, sq_nonneg v]
    have hv2 : v ^ 2 = 0 := by
      nlinarith [sq_nonneg u, sq_nonneg v]
    have hu : u = 0 := sq_eq_zero_iff.mp hu2
    have hv : v = 0 := sq_eq_zero_iff.mp hv2
    exact ⟨hu, hv, by nlinarith⟩
  · rintro ⟨rfl, rfl, hcircle⟩
    simpa using And.intro hcircle hcircle

/-- The displayed intersection contains a point outside all four coordinate directions. -/
theorem split_quadric_inter_sphere_noncardinal :
    ∃ x y : ℝ,
      (x ^ 2 + y ^ 2 - (0 : ℝ) ^ 2 - (0 : ℝ) ^ 2 = 1 ∧
        x ^ 2 + y ^ 2 + (0 : ℝ) ^ 2 + (0 : ℝ) ^ 2 = 1) ∧
      x ≠ 0 ∧ y ≠ 0 := by
  refine ⟨3 / 5, 4 / 5, ?_⟩
  norm_num

end InfoGeometry.Holographic.ArithmeticGeometry
