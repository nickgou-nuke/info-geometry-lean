import InfoGeometry.Canonical.BoundaryBraidRepresentation
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.Cl55CelestialOrderedExchangeRegularBraidMonodromy

/-! The pure-braid restriction of the supplied celestial exchange monodromy.

The permutation quotient is kept separate from the geometric fundamental-group
map: this file adds only the kernel restriction and its three standard pure
generators.
-/
noncomputable section

namespace InfoGeometry.Twistor.Cl55CelestialOrderedExchangePureBraidMonodromy

open InfoGeometry.Canonical.BoundaryBraidRepresentation
open InfoGeometry.Physics.B3PresentedGroup
open InfoGeometry.Twistor.Cl55CelestialOrderedExchangeRegularBraidMonodromy
open InfoGeometry.Twistor.Cl55CelestialOrderedExchangeMonodromy
open InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration
open InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding

def b3Perm0 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
def b3Perm1 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

theorem b3Perm_artin : b3Perm0 * b3Perm1 * b3Perm0 =
    b3Perm1 * b3Perm0 * b3Perm1 := by decide

def b3ToPerm : BoundaryBraidGroup →* Equiv.Perm (Fin 3) :=
  homOfArtinPair b3Perm0 b3Perm1 b3Perm_artin

@[simp] theorem b3ToPerm_sig0 :
    b3ToPerm (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) = b3Perm0 :=
  homOfArtinPair_sig0 _ _ _

@[simp] theorem b3ToPerm_sig1 :
    b3ToPerm (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) = b3Perm1 :=
  homOfArtinPair_sig1 _ _ _

def PureBraidGroup3 : Subgroup BoundaryBraidGroup := MonoidHom.ker b3ToPerm

def pureGenA12 : BoundaryBraidGroup :=
  (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) ^ 2

def pureGenA23 : BoundaryBraidGroup :=
  (PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) ^ 2

def pureGenA13 : BoundaryBraidGroup :=
  (PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup)⁻¹ *
    ((PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) ^ 2) *
      PresentedGroup.of B3Gen.sig0

theorem pureGenA12_mem_pure : pureGenA12 ∈ PureBraidGroup3 := by
  change b3ToPerm ((PresentedGroup.of B3Gen.sig0 : BoundaryBraidGroup) ^ 2) = 1
  rw [map_pow, b3ToPerm_sig0]
  decide

theorem pureGenA23_mem_pure : pureGenA23 ∈ PureBraidGroup3 := by
  change b3ToPerm ((PresentedGroup.of B3Gen.sig1 : BoundaryBraidGroup) ^ 2) = 1
  rw [map_pow, b3ToPerm_sig1]
  decide

theorem pureGenA13_mem_pure : pureGenA13 ∈ PureBraidGroup3 := by
  change b3ToPerm pureGenA13 = 1
  dsimp [pureGenA13]
  rw [map_mul, map_mul, map_inv, map_pow, b3ToPerm_sig0, b3ToPerm_sig1]
  decide

def pureA12 : PureBraidGroup3 := ⟨pureGenA12, pureGenA12_mem_pure⟩
def pureA23 : PureBraidGroup3 := ⟨pureGenA23, pureGenA23_mem_pure⟩
def pureA13 : PureBraidGroup3 := ⟨pureGenA13, pureGenA13_mem_pure⟩

def pureCelestialExchangeClassMap
    (n : ℕ) (p : CelestialOrderedConfiguration n)
    (sigma0 sigma1 : Equiv.Perm (Fin n))
    (gamma0 : @Path (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n) p (celestialPermute n sigma0 p))
    (gamma1 : @Path (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n) p (celestialPermute n sigma1 p))
    (hArtin : celestialOrderedExchangeLoopClass n p sigma0 gamma0 *
        celestialOrderedExchangeLoopClass n p sigma1 gamma1 *
        celestialOrderedExchangeLoopClass n p sigma0 gamma0 =
      celestialOrderedExchangeLoopClass n p sigma1 gamma1 *
        celestialOrderedExchangeLoopClass n p sigma0 gamma0 *
        celestialOrderedExchangeLoopClass n p sigma1 gamma1) :
    PureBraidGroup3 →*
      @FundamentalGroup (CelestialUnorderedConfiguration n)
        (celestialUnorderedConfigurationTopology n) (Quotient.mk' p) :=
  (celestialExchangeClassMap n p sigma0 sigma1 gamma0 gamma1 hArtin).comp
    PureBraidGroup3.subtype

@[simp] theorem pureCelestialExchangeClassMap_A12
    (n : ℕ) (p : CelestialOrderedConfiguration n)
    (sigma0 sigma1 : Equiv.Perm (Fin n))
    (gamma0 : @Path (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n) p (celestialPermute n sigma0 p))
    (gamma1 : @Path (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n) p (celestialPermute n sigma1 p))
    (hArtin : celestialOrderedExchangeLoopClass n p sigma0 gamma0 *
        celestialOrderedExchangeLoopClass n p sigma1 gamma1 *
        celestialOrderedExchangeLoopClass n p sigma0 gamma0 =
      celestialOrderedExchangeLoopClass n p sigma1 gamma1 *
        celestialOrderedExchangeLoopClass n p sigma0 gamma0 *
        celestialOrderedExchangeLoopClass n p sigma1 gamma1) :
    pureCelestialExchangeClassMap n p sigma0 sigma1 gamma0 gamma1 hArtin pureA12 =
      (celestialOrderedExchangeLoopClass n p sigma0 gamma0) ^ 2 := by
  dsimp [pureCelestialExchangeClassMap, pureA12, pureGenA12]
  rw [map_pow, celestialExchangeClassMap_sig0]

end InfoGeometry.Twistor.Cl55CelestialOrderedExchangePureBraidMonodromy
