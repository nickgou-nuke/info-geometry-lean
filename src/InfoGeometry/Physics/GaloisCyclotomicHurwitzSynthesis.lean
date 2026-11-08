/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib.Data.Nat.Totient
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

/-!
# Twelfth cyclotomic roots and finite arithmetic

This owner records native Mathlib facts about primitive twelfth roots and the
unit group modulo 12. It keeps separate the arithmetic counts that happen to
equal 24 from any claimed group isomorphism: this file does not construct a
map from cyclotomic roots to Hurwitz units or to a G₂ root system.
-/

namespace InfoGeometry.Physics.GaloisCyclotomicHurwitzSynthesis

open Polynomial

/-- The `k`th point on the twelfth-root circle, with the standard exponential
parameterization. -/
noncomputable def primitiveTwelfthRoot (k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (k : ℝ) / 12)

/-- The polynomial `X⁴ - X² + 1` is the twelfth cyclotomic polynomial. -/
lemma cyclotomic_twelve (R : Type*) [CommRing R] :
    Polynomial.cyclotomic 12 R = Polynomial.X ^ 4 - Polynomial.X ^ 2 + 1 := by
  rw [show 12 = 6 * 2 by norm_num]
  rw [← Polynomial.cyclotomic_expand_eq_cyclotomic Nat.prime_two
    (by norm_num : 2 ∣ 6) R]
  rw [Polynomial.cyclotomic_six, Polynomial.expand_eq_comp_X_pow]
  simp only [Polynomial.sub_comp, Polynomial.add_comp, Polynomial.pow_comp,
    Polynomial.X_comp, Polynomial.one_comp]
  ring

/-- A parameter coprime to 12 gives a primitive twelfth root. -/
lemma primitiveTwelfthRoot_isPrimitiveRoot (k : ℕ) (hk : k.Coprime 12) :
    IsPrimitiveRoot (primitiveTwelfthRoot k) 12 := by
  convert Complex.isPrimitiveRoot_exp_of_coprime k 12 (by norm_num) hk using 1
  simp [primitiveTwelfthRoot, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- The explicit polynomial value agrees with evaluation of Mathlib's
cyclotomic polynomial. -/
lemma phi12_eq_cyclotomic_eval (z : ℂ) :
    z ^ 4 - z ^ 2 + 1 = (Polynomial.cyclotomic 12 ℂ).eval z := by
  rw [cyclotomic_twelve]
  simp only [Polynomial.eval_sub, Polynomial.eval_add, Polynomial.eval_pow,
    Polynomial.eval_X, Polynomial.eval_one]

/-- Every parameter coprime to 12 gives a root of `X⁴ - X² + 1`. -/
lemma primitiveTwelfthRoot_isRootPhi12 (k : ℕ) (hk : k.Coprime 12) :
    (primitiveTwelfthRoot k) ^ 4 - (primitiveTwelfthRoot k) ^ 2 + 1 = 0 := by
  rw [phi12_eq_cyclotomic_eval]
  exact (primitiveTwelfthRoot_isPrimitiveRoot k hk).isRoot_cyclotomic (by norm_num)

/-- A complex number is a root of `X⁴ - X² + 1` exactly when it is a primitive
twelfth root of unity. -/
lemma isRootPhi12_iff_isPrimitiveRoot (z : ℂ) :
    z ^ 4 - z ^ 2 + 1 = 0 ↔ IsPrimitiveRoot z 12 := by
  rw [phi12_eq_cyclotomic_eval]
  change (Polynomial.cyclotomic 12 ℂ).IsRoot z ↔ IsPrimitiveRoot z 12
  exact Polynomial.isRoot_cyclotomic_iff

/-- Mathlib's cyclotomic-root theorem identifies the roots of `Φ₁₂` with the
primitive twelfth roots; their cardinality is Euler's totient `φ(12) = 4`. -/
lemma phi12RootCount : (Polynomial.cyclotomic 12 ℂ).roots.card = 4 := by
  rw [Polynomial.cyclotomic.roots_eq_primitiveRoots_val]
  change (primitiveRoots 12 ℂ).card = 4
  rw [Complex.card_primitiveRoots]
  decide

/-- The primitive twelfth roots form a Galois orbit under raising to
exponents coprime to 12. This is the orbit statement on roots; no field
automorphism structure is asserted here. -/
lemma primitiveTwelfthRoot_orbit_transitive [NeZero 12] {a b : ℕ}
    (ha : a.Coprime 12) (hb : b.Coprime 12) :
    ∃ p : ℕ, p.Coprime 12 ∧
      primitiveTwelfthRoot b = (primitiveTwelfthRoot a) ^ p := by
  have hA := primitiveTwelfthRoot_isPrimitiveRoot a ha
  have hB := primitiveTwelfthRoot_isPrimitiveRoot b hb
  obtain ⟨p, hp_lt, hp, hEq⟩ := hA.isPrimitiveRoot_iff.mp hB
  exact ⟨p, hp, hEq.symm⟩

/-- The unit group modulo 12 has four elements, computed through Mathlib's
totient cardinality theorem. -/
lemma galoisGroupOrder12 : Fintype.card (ZMod 12)ˣ = 4 := by
  rw [ZMod.card_units_eq_totient]
  decide

/-- The two elementary cardinality identities often used alongside the
twelfth-root discussion. They are numerical equalities only. -/
lemma hurwitzAndRootCountArithmetic :
    (8 : ℕ) + 16 = 24 ∧ 6 + 6 = 12 ∧ 12 * 2 = 24 ∧ 6 * 4 = 24 := by
  norm_num

end InfoGeometry.Physics.GaloisCyclotomicHurwitzSynthesis
