import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Arithmetic.PrimeCyclotomicGaloisFieldTower

/-!
# Galois-group readout of the fixed prime cyclotomic tower

For every stage `K_N = ℚ(ζ_N)`, Mathlib identifies the group of `ℚ`-algebra
automorphisms with `(ZMod N)ˣ`.  The divisibility maps of conductors induce
contravariant unit-group homomorphisms.  We transport these maps through the
Galois/unit equivalences to obtain a canonical inverse group tower.

The transported maps below are not asserted to be literal restriction maps
along the particular field embeddings chosen in `PrimeCyclotomicGaloisFieldTower`;
that compatibility is stated as a separate frontier.
-/

noncomputable section

namespace InfoGeometry.Arithmetic.PrimeCyclotomicGaloisGroupTower

open InfoGeometry.Arithmetic.PrimeCyclotomicGaloisDirectedClosure
open InfoGeometry.Arithmetic.PrimeCyclotomicGaloisFieldTower

/-- Native cyclotomic Galois-group equivalences. -/
def gal2EquivUnits : (K2 ≃ₐ[ℚ] K2) ≃* (ZMod 2)ˣ :=
  IsCyclotomicExtension.autEquivPow K2
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

def gal6EquivUnits : (K6 ≃ₐ[ℚ] K6) ≃* (ZMod 6)ˣ :=
  IsCyclotomicExtension.autEquivPow K6
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

def gal30EquivUnits : (K30 ≃ₐ[ℚ] K30) ≃* (ZMod 30)ˣ :=
  IsCyclotomicExtension.autEquivPow K30
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

def gal210EquivUnits : (K210 ≃ₐ[ℚ] K210) ≃* (ZMod 210)ˣ :=
  IsCyclotomicExtension.autEquivPow K210
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

def gal2310EquivUnits : (K2310 ≃ₐ[ℚ] K2310) ≃* (ZMod 2310)ˣ :=
  IsCyclotomicExtension.autEquivPow K2310
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

def gal30030EquivUnits : (K30030 ≃ₐ[ℚ] K30030) ≃* (ZMod 30030)ˣ :=
  IsCyclotomicExtension.autEquivPow K30030
    (Polynomial.cyclotomic.irreducible_rat (by norm_num))

/-- Contravariant arithmetic transition maps on the unit-group models. -/
def units6To2 : (ZMod 6)ˣ →* (ZMod 2)ˣ := ZMod.unitsMap conductor_dvd_01
def units30To6 : (ZMod 30)ˣ →* (ZMod 6)ˣ := ZMod.unitsMap conductor_dvd_12
def units210To30 : (ZMod 210)ˣ →* (ZMod 30)ˣ := ZMod.unitsMap conductor_dvd_23
def units2310To210 : (ZMod 2310)ˣ →* (ZMod 210)ˣ := ZMod.unitsMap conductor_dvd_34
def units30030To2310 : (ZMod 30030)ˣ →* (ZMod 2310)ˣ := ZMod.unitsMap conductor_dvd_45

/-- Galois transition transported through the canonical unit-group models. -/
def gal6To2 : (K6 ≃ₐ[ℚ] K6) →* (K2 ≃ₐ[ℚ] K2) :=
  gal2EquivUnits.symm.toMonoidHom.comp
    (units6To2.comp gal6EquivUnits.toMonoidHom)

def gal30To6 : (K30 ≃ₐ[ℚ] K30) →* (K6 ≃ₐ[ℚ] K6) :=
  gal6EquivUnits.symm.toMonoidHom.comp
    (units30To6.comp gal30EquivUnits.toMonoidHom)

def gal210To30 : (K210 ≃ₐ[ℚ] K210) →* (K30 ≃ₐ[ℚ] K30) :=
  gal30EquivUnits.symm.toMonoidHom.comp
    (units210To30.comp gal210EquivUnits.toMonoidHom)

def gal2310To210 : (K2310 ≃ₐ[ℚ] K2310) →* (K210 ≃ₐ[ℚ] K210) :=
  gal210EquivUnits.symm.toMonoidHom.comp
    (units2310To210.comp gal2310EquivUnits.toMonoidHom)

def gal30030To2310 : (K30030 ≃ₐ[ℚ] K30030) →* (K2310 ≃ₐ[ℚ] K2310) :=
  gal2310EquivUnits.symm.toMonoidHom.comp
    (units30030To2310.comp gal30030EquivUnits.toMonoidHom)

/-- Each transported transition is exactly the corresponding `ZMod.unitsMap`
after applying the cyclotomic Galois identifications. -/
theorem gal6To2_unit_readback (σ : K6 ≃ₐ[ℚ] K6) :
    gal2EquivUnits (gal6To2 σ) = units6To2 (gal6EquivUnits σ) := by
  simp [gal6To2]

theorem gal30To6_unit_readback (σ : K30 ≃ₐ[ℚ] K30) :
    gal6EquivUnits (gal30To6 σ) = units30To6 (gal30EquivUnits σ) := by
  simp [gal30To6]

theorem gal210To30_unit_readback (σ : K210 ≃ₐ[ℚ] K210) :
    gal30EquivUnits (gal210To30 σ) = units210To30 (gal210EquivUnits σ) := by
  simp [gal210To30]

theorem gal2310To210_unit_readback (σ : K2310 ≃ₐ[ℚ] K2310) :
    gal210EquivUnits (gal2310To210 σ) = units2310To210 (gal2310EquivUnits σ) := by
  simp [gal2310To210]

theorem gal30030To2310_unit_readback (σ : K30030 ≃ₐ[ℚ] K30030) :
    gal2310EquivUnits (gal30030To2310 σ) =
      units30030To2310 (gal30030EquivUnits σ) := by
  simp [gal30030To2310]

/-- The complete inverse Galois tower as five explicit group homomorphisms. -/
structure PrimeCyclotomicGaloisInverseTower where
  r10 : (K6 ≃ₐ[ℚ] K6) →* (K2 ≃ₐ[ℚ] K2)
  r21 : (K30 ≃ₐ[ℚ] K30) →* (K6 ≃ₐ[ℚ] K6)
  r32 : (K210 ≃ₐ[ℚ] K210) →* (K30 ≃ₐ[ℚ] K30)
  r43 : (K2310 ≃ₐ[ℚ] K2310) →* (K210 ≃ₐ[ℚ] K210)
  r54 : (K30030 ≃ₐ[ℚ] K30030) →* (K2310 ≃ₐ[ℚ] K2310)

/-- Canonical arithmetic inverse tower induced by conductor reduction. -/
def galoisInverseTower : PrimeCyclotomicGaloisInverseTower where
  r10 := gal6To2
  r21 := gal30To6
  r32 := gal210To30
  r43 := gal2310To210
  r54 := gal30030To2310

end InfoGeometry.Arithmetic.PrimeCyclotomicGaloisGroupTower
