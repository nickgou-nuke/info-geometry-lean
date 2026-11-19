/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
import Mathlib.RingTheory.Trace.Basic
import InfoGeometry.Canonical.TwelveFoldCyclotomicNative
import InfoGeometry.Canonical.TwelveFoldGaloisCharacterSets

/-!
# Cyclotomic harmonic Galois action and integral orbit sums

The carrier is Mathlib's `CyclotomicField n ℚ`. Its canonical primitive root
defines a native additive character on `ZMod n`. Native field automorphisms
permute harmonic frequencies by multiplication by the corresponding unit.

The Ramanujan sum below is the actual sum of these character values over the
units modulo `n`. It equals the field trace of a root of unity and is an
integer because that root and its trace are integral over `ℤ`. Fixedness under
the Galois action alone would establish rationality, not integrality.

An orbit sum is one function associated with an order shell. No claim that
these sums form a basis of each full harmonic shell is made. The divisor
degree count is not asserted to construct a direct-sum decomposition. The
Möbius divisor formula for the Ramanujan sum is a separate theorem.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.CyclotomicHarmonicOrbits

open scoped BigOperators

variable (n : ℕ) [NeZero n]

local instance : NeZero (n : ℚ) :=
  ⟨Nat.cast_ne_zero.mpr (NeZero.ne n)⟩

local instance : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) :=
  CyclotomicField.isCyclotomicExtension n ℚ

/-- The additive character defined by the native primitive cyclotomic root. -/
def cyclotomicCharacter : AddChar (ZMod n) (CyclotomicField n ℚ) :=
  AddChar.zmodChar n
    (IsCyclotomicExtension.zeta_pow n ℚ (CyclotomicField n ℚ))

/-- The frequency-`k` phase at cyclic position `x`. -/
def cyclotomicPhase (k x : ZMod n) : CyclotomicField n ℚ :=
  cyclotomicCharacter n (k * x)

/-- Every character value is an `n`th root of unity. -/
theorem cyclotomicCharacter_pow (x : ZMod n) :
    cyclotomicCharacter n x ^ n = 1 := by
  change (IsCyclotomicExtension.zeta n ℚ (CyclotomicField n ℚ) ^ x.val) ^ n = 1
  rw [pow_right_comm, IsCyclotomicExtension.zeta_pow, one_pow]

/-- Root-of-unity integrality is supplied by its monic polynomial. -/
theorem cyclotomicCharacter_isIntegral (x : ZMod n) :
    IsIntegral ℤ (cyclotomicCharacter n x) := by
  exact ((IsCyclotomicExtension.zeta_spec n ℚ (CyclotomicField n ℚ)).isIntegral
    (NeZero.pos n)).pow x.val

/-- The actual permutation of cyclic frequencies induced by a field automorphism. -/
def galoisFrequencyPermutation (σ : Gal(CyclotomicField n ℚ / ℚ)) :
    Equiv.Perm (ZMod n) :=
  (IsCyclotomicExtension.Rat.galEquivZMod n (CyclotomicField n ℚ) σ).mulLeft

/-- Native Galois action equals multiplication of the character's residue argument. -/
theorem galois_cyclotomicCharacter
    (σ : Gal(CyclotomicField n ℚ / ℚ)) (x : ZMod n) :
    σ (cyclotomicCharacter n x) =
      cyclotomicCharacter n
        ((IsCyclotomicExtension.Rat.galEquivZMod n (CyclotomicField n ℚ) σ :
          ZMod n) * x) := by
  rw [IsCyclotomicExtension.Rat.galEquivZMod_apply_of_pow_eq n
    (CyclotomicField n ℚ) σ (cyclotomicCharacter_pow n x)]
  simpa only [nsmul_eq_mul, ZMod.natCast_zmod_val] using
    ((cyclotomicCharacter n).map_nsmul_eq_pow
      (IsCyclotomicExtension.Rat.galEquivZMod n (CyclotomicField n ℚ) σ).val.val x).symm

/-- The field action and frequency permutation commute with harmonic evaluation. -/
theorem galois_cyclotomicPhase
    (σ : Gal(CyclotomicField n ℚ / ℚ)) (k x : ZMod n) :
    σ (cyclotomicPhase n k x) =
      cyclotomicPhase n (galoisFrequencyPermutation n σ k) x := by
  simpa only [cyclotomicPhase, galoisFrequencyPermutation, Units.mulLeft_apply,
    mul_assoc] using galois_cyclotomicCharacter n σ (k * x)

/-- Composition of field automorphisms induces composition of frequency permutations. -/
theorem galoisFrequencyPermutation_mul
    (σ τ : Gal(CyclotomicField n ℚ / ℚ)) :
    galoisFrequencyPermutation n (σ * τ) =
      galoisFrequencyPermutation n σ * galoisFrequencyPermutation n τ := by
  ext k
  simp [galoisFrequencyPermutation, mul_assoc]

/-- The native frequency action preserves each shell of a given exact additive order. -/
theorem galoisFrequencyPermutation_addOrderOf
    (σ : Gal(CyclotomicField n ℚ / ℚ)) (k : ZMod n) :
    addOrderOf (galoisFrequencyPermutation n σ k) = addOrderOf k := by
  let u := IsCyclotomicExtension.Rat.galEquivZMod n (CyclotomicField n ℚ) σ
  change addOrderOf (LinearEquiv.smulOfUnit (R := ZMod n) (M := ZMod n) u k) =
    addOrderOf k
  exact (LinearEquiv.smulOfUnit (R := ZMod n) (M := ZMod n) u).toAddEquiv.addOrderOf_eq k

/-- Sum over all primitive frequency labels, with multiplicity after evaluation at `x`. -/
def cyclotomicRamanujanSum (x : ZMod n) : CyclotomicField n ℚ :=
  ∑ u : (ZMod n)ˣ, cyclotomicCharacter n ((u : ZMod n) * x)

/-- The unit orbit sum is the native field trace, embedded back into the cyclotomic field. -/
theorem cyclotomicRamanujanSum_eq_trace (x : ZMod n) :
    cyclotomicRamanujanSum n x =
      algebraMap ℚ (CyclotomicField n ℚ)
        (Algebra.trace ℚ (CyclotomicField n ℚ) (cyclotomicCharacter n x)) := by
  let : IsGalois ℚ (CyclotomicField n ℚ) :=
    IsCyclotomicExtension.isGalois {n} ℚ (CyclotomicField n ℚ)
  rw [trace_eq_sum_automorphisms]
  exact (Fintype.sum_equiv
    (IsCyclotomicExtension.Rat.galEquivZMod n (CyclotomicField n ℚ)).toEquiv
    (fun σ => σ (cyclotomicCharacter n x))
    (fun u => cyclotomicCharacter n ((u : ZMod n) * x))
    (fun σ => galois_cyclotomicCharacter n σ x)).symm

/-- Integrality of the root and of its field trace makes the orbit sum an integer. -/
theorem cyclotomicRamanujanSum_isInteger (x : ZMod n) :
    ∃ z : ℤ, cyclotomicRamanujanSum n x = (z : CyclotomicField n ℚ) := by
  have htrace : IsIntegral ℤ
      (Algebra.trace ℚ (CyclotomicField n ℚ) (cyclotomicCharacter n x)) :=
    Algebra.isIntegral_trace (cyclotomicCharacter_isIntegral n x)
  obtain ⟨z, hz⟩ := (IsIntegrallyClosed.isIntegral_iff (R := ℤ) (K := ℚ)).mp htrace
  refine ⟨z, ?_⟩
  rw [cyclotomicRamanujanSum_eq_trace, ← hz]
  simp

/-- Every native Galois automorphism fixes the orbit sum. -/
theorem cyclotomicRamanujanSum_galois_fixed
    (σ : Gal(CyclotomicField n ℚ / ℚ)) (x : ZMod n) :
    σ (cyclotomicRamanujanSum n x) = cyclotomicRamanujanSum n x := by
  rw [cyclotomicRamanujanSum_eq_trace]
  exact σ.commutes _

/-- Multiplication of the residue by a unit only reindexes the orbit sum. -/
theorem cyclotomicRamanujanSum_mul_unit (u : (ZMod n)ˣ) (x : ZMod n) :
    cyclotomicRamanujanSum n ((u : ZMod n) * x) = cyclotomicRamanujanSum n x := by
  unfold cyclotomicRamanujanSum
  simpa only [Equiv.coe_mulRight, Units.val_mul, mul_assoc] using
    Equiv.sum_comp (Equiv.mulRight u)
      (fun v : (ZMod n)ˣ => cyclotomicCharacter n ((v : ZMod n) * x))

/-- At the zero residue every summand is one, giving Euler's totient. -/
theorem cyclotomicRamanujanSum_zero :
    cyclotomicRamanujanSum n 0 = (n.totient : CyclotomicField n ℚ) := by
  simp [cyclotomicRamanujanSum, ZMod.card_units_eq_totient]

omit [NeZero n] in
/-- The dimensions of the cyclotomic fields indexed by divisors sum to `n`.
This counts dimensions; it does not construct a decomposition of a Fourier space. -/
theorem sum_cyclotomic_finrank_divisors :
    ∑ d ∈ n.divisors, Module.finrank ℚ (CyclotomicField d ℚ) = n := by
  calc
    _ = ∑ d ∈ n.divisors, d.totient := by
      apply Finset.sum_congr rfl
      intro d hd
      let : NeZero d := ⟨(Nat.pos_of_mem_divisors hd).ne'⟩
      exact IsCyclotomicExtension.Rat.finrank d (CyclotomicField d ℚ)
    _ = n := Nat.sum_totient n

section Twelve

open InfoGeometry.Canonical.TwelveFoldCyclotomicNative
open InfoGeometry.Canonical.TwelveFoldGaloisCharacterSets

/-- The genuine field automorphism corresponding to the existing unit `5 mod 12`. -/
def cyclotomic12UnitFiveAutomorphism : Gal(CyclotomicField 12 ℚ / ℚ) :=
  cyclotomic12_galEquivUnits.symm sigma5

/-- Unit five acts on every twelfth harmonic by its arithmetic frequency permutation. -/
theorem cyclotomic12UnitFive_phase (k x : ZMod 12) :
    cyclotomic12UnitFiveAutomorphism (cyclotomicPhase 12 k x) =
      cyclotomicPhase 12 (5 * k) x := by
  have hσ :
      IsCyclotomicExtension.Rat.galEquivZMod 12 (CyclotomicField 12 ℚ)
        cyclotomic12UnitFiveAutomorphism = sigma5 := by
    change cyclotomic12_galEquivUnits (cyclotomic12_galEquivUnits.symm sigma5) = sigma5
    exact cyclotomic12_galEquivUnits.apply_symm_apply sigma5
  have hfive : (sigma5 : ZMod 12) = 5 := rfl
  simpa only [galoisFrequencyPermutation, hσ, Units.mulLeft_apply, hfive] using
    galois_cyclotomicPhase 12 cyclotomic12UnitFiveAutomorphism k x

theorem cyclotomic12UnitFive_phase_one (x : ZMod 12) :
    cyclotomic12UnitFiveAutomorphism (cyclotomicPhase 12 1 x) =
      cyclotomicPhase 12 5 x := by
  simpa only [mul_one] using cyclotomic12UnitFive_phase 1 x

theorem cyclotomic12UnitFive_phase_five (x : ZMod 12) :
    cyclotomic12UnitFiveAutomorphism (cyclotomicPhase 12 5 x) =
      cyclotomicPhase 12 1 x := by
  simpa only [show (5 : ZMod 12) * 5 = 1 by decide] using
    cyclotomic12UnitFive_phase 5 x

theorem cyclotomic12UnitFive_phase_three (x : ZMod 12) :
    cyclotomic12UnitFiveAutomorphism (cyclotomicPhase 12 3 x) =
      cyclotomicPhase 12 3 x := by
  simpa only [show (5 : ZMod 12) * 3 = 3 by decide] using
    cyclotomic12UnitFive_phase 3 x

theorem cyclotomic12UnitFive_phase_six (x : ZMod 12) :
    cyclotomic12UnitFiveAutomorphism (cyclotomicPhase 12 6 x) =
      cyclotomicPhase 12 6 x := by
  simpa only [show (5 : ZMod 12) * 6 = 6 by decide] using
    cyclotomic12UnitFive_phase 6 x

end Twelve

end InfoGeometry.Arithmetic.CyclotomicHarmonicOrbits
