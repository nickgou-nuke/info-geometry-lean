import Mathlib.NumberTheory.LegendreSymbol.AddCharacter
import Mathlib.RingTheory.RootsOfUnity.Complex
import InfoGeometry.Canonical.TwelveFoldArithmeticNative

/-!
# The additive character carried by the twelvefold phase

This owner formalizes the finite additive/cyclotomic character layer.  Its
domain is `ZMod 12` with cardinality `12`; it is therefore distinct from the
multiplicative unit group `(ZMod 12)ˣ`, whose cardinality is `4` and which is
the domain of Galois/Dirichlet character data.
-/

noncomputable section

namespace InfoGeometry.Canonical.TwelveFoldAdditiveCharacter

open Complex

def zeta12 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 12)

theorem zeta12_primitive : IsPrimitiveRoot zeta12 12 := by
  exact Complex.isPrimitiveRoot_exp 12 (by norm_num)

theorem zeta12_pow_twelve : zeta12 ^ 12 = 1 :=
  zeta12_primitive.pow_eq_one

def additiveCharacter12 : AddChar (ZMod 12) ℂ :=
  AddChar.zmodChar 12 zeta12_pow_twelve

@[simp] theorem additiveCharacter12_apply (a : ZMod 12) :
    additiveCharacter12 a = zeta12 ^ a.val := by
  rfl

theorem additiveCharacter12_primitive : AddChar.IsPrimitive additiveCharacter12 := by
  exact AddChar.zmodChar_primitive_of_primitive_root 12 zeta12_primitive

theorem additiveCharacter12_ne_one : additiveCharacter12 ≠ 1 := by
  rw [AddChar.zmod_char_ne_one_iff]
  rw [additiveCharacter12_apply]
  change zeta12 ^ 1 ≠ 1
  simpa using zeta12_primitive.ne_one (by norm_num)

theorem additive_domain_card : Fintype.card (ZMod 12) = 12 := by
  decide

theorem multiplicative_domain_card : Fintype.card (ZMod 12)ˣ = 4 := by
  exact InfoGeometry.Canonical.TwelveFoldArithmeticNative.zmod12_units_card

theorem additive_and_multiplicative_domains_differ :
    Fintype.card (ZMod 12) ≠ Fintype.card (ZMod 12)ˣ := by
  rw [additive_domain_card, multiplicative_domain_card]
  norm_num

theorem additiveCharacter12_value_zero : additiveCharacter12 0 = 1 := by
  simp

theorem additiveCharacter12_value_one : additiveCharacter12 1 = zeta12 := by
  rw [additiveCharacter12_apply]
  change zeta12 ^ 1 = zeta12
  exact pow_one _

end InfoGeometry.Canonical.TwelveFoldAdditiveCharacter
end noncomputable section
