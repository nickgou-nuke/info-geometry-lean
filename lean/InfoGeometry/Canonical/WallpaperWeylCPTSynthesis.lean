/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/
import Mathlib
import InfoGeometry.Canonical.WallpaperParityBooleanBridge
import InfoGeometry.Canonical.WeylCPTParityBridge
import InfoGeometry.Canonical.KleinGlideTwistedCommutantBridge

/-!
# Wallpaper parity, Weyl sign, and CPT parity on one carrier

The square lattice parity bits are identified with the two-generator Weyl
group of the primes {2,3}. Its sign is the CPT bivector parity, while the
wallpaper diagonal reflection is the corresponding coordinate permutation.
-/
namespace InfoGeometry.Canonical.WallpaperWeylCPTSynthesis

open InfoGeometry.Algebra
open InfoGeometry.Canonical.WallpaperAffineWeylD5Bridge
open InfoGeometry.Canonical.WeylSignum
open InfoGeometry.Canonical.WallpaperParityBooleanBridge
open InfoGeometry.Canonical.WeylCPTParityBridge
open InfoGeometry.Canonical.KleinBottleTwistedCommutant

/-- The two-prime A₁² root system. -/
def twoPrimeSystem : PrimeA1RootSystem where
  P := {2, 3}
  all_prime := by
    intro p hp
    simp at hp
    rcases hp with rfl | rfl <;> norm_num

/-- The two Weyl simple reflections as elements of the root system support. -/
def p2 : {p // p ∈ twoPrimeSystem.P} := ⟨2, by simp [twoPrimeSystem]⟩
def p3 : {p // p ∈ twoPrimeSystem.P} := ⟨3, by simp [twoPrimeSystem]⟩

theorem p2_ne_p3 : p2 ≠ p3 := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num [p2, p3] at hv

/-- Map a parity bit vector to the corresponding Weyl reflection subset. -/
def parityToWeyl (b : Fin 2 → Bool) : Finset {p // p ∈ twoPrimeSystem.P} :=
  (if b 0 = true then ({p2} : Finset {p // p ∈ twoPrimeSystem.P}) else (∅ : Finset {p // p ∈ twoPrimeSystem.P})) ∪
    (if b 1 = true then ({p3} : Finset {p // p ∈ twoPrimeSystem.P}) else ∅)

theorem parityToWeyl_card (b : Fin 2 → Bool) :
    (parityToWeyl b).card = (if b 0 = true then 1 else 0) + (if b 1 = true then 1 else 0) := by
  by_cases h0 : b 0 = true <;> by_cases h1 : b 1 = true <;>
    simp [parityToWeyl, h0, h1, p2_ne_p3]

/-- The Weyl sign of a lattice parity class is +1 iff the two parity bits agree. -/
theorem wallpaperParity_weylSignum (t : ℤ × ℤ) :
    weylSignum (parityToWeyl (wallpaperParity t)) =
      if t.1.bodd = t.2.bodd then (1 : ℤ) else -1 := by
  by_cases h0 : t.1.bodd = true <;> by_cases h1 : t.2.bodd = true <;>
    simp [parityToWeyl, parityToWeyl_card, wallpaperParity, weylSignum,
      PrimeA1RootSystem.signature, h0, h1, p2_ne_p3]

/-- The same sign is the CPT bivector parity of the associated Weyl element. -/
theorem wallpaperParity_cptParity (t : ℤ × ℤ) :
    weylSignum (parityToWeyl (wallpaperParity t)) =
      if (parityToWeyl (wallpaperParity t)).card % 2 = 0 then (1 : ℤ) else -1 :=
  weylSignum_eq_parity _

end InfoGeometry.Canonical.WallpaperWeylCPTSynthesis
