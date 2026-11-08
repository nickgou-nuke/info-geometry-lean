/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import InfoGeometry.Quantum.KitaevChain
import InfoGeometry.PinMinus88Triality.PinMinus88TrialityPoset

/-!
# Kitaev chain parity and the Pin-minus mod-8 arithmetic interface

This file makes the shared finite coefficient system explicit: the Kitaev
chain owner assigns a gapped chain a `ZMod 2` sign parity, while the Pin-minus
owner contains arithmetic in `ZMod 8` and the `ZMod 24` CRT split. The map
below is the canonical reduction `ZMod 8 → ZMod 2`. The results here are only
about these finite groups and the chain owner's parity operation; they do not
construct an ABK bordism invariant or a Fidkowski–Kitaev classification map.
-/

namespace InfoGeometry.Canonical.KitaevPinMinusParityArithmeticBridge

open InfoGeometry.Quantum.KitaevChain

/-- The algebraic quotient map from a free integer label to its residue mod eight.
This is the coefficient map suggested by the BDI `ℤ → ℤ₈` reduction; it does
not by itself construct a map on physical phases. -/
def bdiIntegerToPinMinusEight : ℤ →+* ZMod 8 :=
  Int.castRingHom (ZMod 8)

/-- Every mod-eight label is represented by an integer. -/
theorem bdiIntegerToPinMinusEight_surjective :
    Function.Surjective bdiIntegerToPinMinusEight :=
  ZMod.intCast_surjective

/-- The kernel of the integer residue map is exactly `8ℤ`. -/
theorem bdiIntegerToPinMinusEight_eq_zero_iff (n : ℤ) :
    bdiIntegerToPinMinusEight n = 0 ↔ (8 : ℤ) ∣ n := by
  exact ZMod.intCast_zmod_eq_zero_iff_dvd n 8

/-- Reduction of an eight-valued residue to its mod-two parity. -/
def pinMinusEightToClassD : ZMod 8 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 8) (ZMod 2)

/-- Reducing an integer modulo eight and then taking parity agrees with direct
reduction modulo two. This is the arithmetic factorization `ℤ → ℤ₈ → ℤ₂`. -/
theorem bdi_integer_reduction_factors_through_mod8 (n : ℤ) :
    pinMinusEightToClassD (bdiIntegerToPinMinusEight n) = (n : ZMod 2) := by
  have hcomp : pinMinusEightToClassD.comp bdiIntegerToPinMinusEight =
      Int.castRingHom (ZMod 2) := RingHom.ext_int _ _
  exact congrArg (fun f : ℤ →+* ZMod 2 => f n) hcomp

/-- The same CRT map used by `zmod24_chinese_remainder_abk_triality_split` in
the Pin-minus owner, kept bundled for reuse by this bridge. -/
def pinMinus24ToFactors : ZMod 24 ≃+* ZMod 8 × ZMod 3 :=
  ZMod.chineseRemainder (by norm_num : Nat.Coprime 8 3)

/-- Direct reduction of a 24-residue to class-D parity. -/
def pinMinus24ToClassD : ZMod 24 →+* ZMod 2 :=
  ZMod.castHom (by norm_num : 2 ∣ 24) (ZMod 2)

/-- The class-D parity of a 24-residue is exactly the reduction of its `ZMod 8`
CRT coordinate. The `ZMod 3` triality coordinate is forgotten by this map. -/
theorem pinMinus24_parity_factors_through_mod8 (x : ZMod 24) :
    pinMinus24ToClassD x =
      pinMinusEightToClassD (pinMinus24ToFactors x).1 := by
  let f : ZMod 24 →+* ZMod 2 :=
    pinMinusEightToClassD.comp
      ((RingHom.fst (ZMod 8) (ZMod 3)).comp pinMinus24ToFactors.toRingHom)
  have hf : f = pinMinus24ToClassD := RingHom.ext_zmod f pinMinus24ToClassD
  exact congrArg (fun g : ZMod 24 →+* ZMod 2 => g x) hf.symm

/-- The mod-eight parity projection is surjective. -/
theorem pinMinusEightToClassD_surjective :
    Function.Surjective pinMinusEightToClassD :=
  ZMod.castHom_surjective (by norm_num : 2 ∣ 8)

/-- The map forgets information: residues zero and two have the same parity. -/
theorem pinMinusEightToClassD_not_injective :
    ¬ Function.Injective pinMinusEightToClassD := by
  intro hinj
  have hzero : pinMinusEightToClassD (0 : ZMod 8) =
      pinMinusEightToClassD (2 : ZMod 8) := by decide
  have : (0 : ZMod 8) = 2 := hinj hzero
  exact (by decide : (0 : ZMod 8) ≠ 2) this

/-- There is no residue of additive order at most two in `ZMod 8` whose
reduction has odd parity. This finite calculation is the obstruction behind
the failure of an additive section. -/
theorem no_order_two_odd_residue (z : ZMod 8)
    (hz : z + z = 0) (hodd : pinMinusEightToClassD z = 1) : False := by
  have hfinite : ∀ z : ZMod 8,
      z + z = 0 → pinMinusEightToClassD z = 1 → False := by
    decide
  exact hfinite z hz hodd

/-- The parity reduction `ZMod 8 → ZMod 2` has no additive section. Hence an
arithmetic lift of an individual class-D parity cannot be promoted to a
homomorphic class-D-to-`ZMod 8` comparison without additional structure. -/
theorem pinMinusEightToClassD_no_additive_section
    (s : ZMod 2 →+ ZMod 8) :
    ¬ ∀ x : ZMod 2, pinMinusEightToClassD (s x) = x := by
  intro hs
  have htwo : (1 : ZMod 2) + 1 = 0 := by decide
  have hdouble : s 1 + s 1 = 0 := by
    have h := congrArg s htwo
    simpa only [map_add, map_zero] using h
  exact no_order_two_odd_residue (s 1) hdouble (hs 1)

/-- Every finite chain parity has a mod-eight arithmetic lift. This is only a
surjectivity statement for the coefficient map; it does not choose a
topological phase lift. -/
theorem chain_parity_has_mod8_lift (chain : List KitaevCell) :
    ∃ z : ZMod 8, pinMinusEightToClassD z = topologicalIndexZ2 chain :=
  pinMinusEightToClassD_surjective (topologicalIndexZ2 chain)

/-- Conditional compatibility of the chain fusion law with mod-eight
reduction: if two chosen residues reduce to the two chain parities, their sum
reduces to the parity of the concatenated gapped chains. The hypotheses are
the explicit cross-lane identification; this theorem does not construct it. -/
theorem chain_fusion_compatible_with_mod8_reduction
    (chain₁ chain₂ : List KitaevCell) (z₁ z₂ : ZMod 8)
    (h₁ : macroscopicVolume chain₁ ≠ 0)
    (h₂ : macroscopicVolume chain₂ ≠ 0)
    (hz₁ : pinMinusEightToClassD z₁ = topologicalIndexZ2 chain₁)
    (hz₂ : pinMinusEightToClassD z₂ = topologicalIndexZ2 chain₂) :
    pinMinusEightToClassD (z₁ + z₂) = topologicalIndexZ2 (chain₁ ++ chain₂) := by
  rw [map_add, hz₁, hz₂,
    topologicalIndexZ2_append_of_macroscopicVolume_ne_zero chain₁ chain₂ h₁ h₂]

end InfoGeometry.Canonical.KitaevPinMinusParityArithmeticBridge
