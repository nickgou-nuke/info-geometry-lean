import InfoGeometry.Twistor.Cl55CelestialConfigurationCovering
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.ProjectiveNullConfigurationCoveringLocalSystem

/-!
# Direct local system of the concrete celestial configuration covering

The ambient `Q55` covering local system and its celestial pullback are useful
for comparison with the full projective-null carrier.  This owner records the
independent direct covering local system whose fiber is the free module on
ordered celestial lifts of an unordered configuration.

No identification with a conformal-block system, braid representation, or
anyon theory is asserted here.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55CelestialConfigurationCoveringLocalSystem

open CategoryTheory
open InfoGeometry.Twistor.Cl55CelestialConfigurationCovering
open InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration
open InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding
open InfoGeometry.Twistor.ProjectiveNullConfigurationCoveringLocalSystem
open InfoGeometry.Twistor.ProjectiveNullConfigurationLocalSystemMonodromy
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology

variable {R : Type*} [Ring R]

abbrev CelestialConfigurationLocalSystem (R : Type*) [Ring R] (n : ℕ) :=
  let _inst : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  FundamentalGroupoid (CelestialUnorderedConfiguration n) ⥤ ModuleCat R

def celestialConfigurationCoveringLocalSystem
    (R : Type*) [Ring R] (n : ℕ) :
    CelestialConfigurationLocalSystem R n := by
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  exact coveringFiberLinearLocalSystem R
    (celestialUnorderedProjection_isQuotientCoveringMap n).isCoveringMap

def celestialConfigurationCoveringIsCoveringMap (n : ℕ) :
    @IsCoveringMap
      (CelestialOrderedConfiguration n)
      (CelestialUnorderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      (celestialUnorderedConfigurationTopology n)
      (@Quotient.mk' (CelestialOrderedConfiguration n)
        (celestialReindexSetoid n)) := by
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  exact (celestialUnorderedProjection_isQuotientCoveringMap n).isCoveringMap

def celestialConfigurationCoveringMonodromy
    (R : Type*) [Ring R] (n : ℕ)
    (p : CelestialUnorderedConfiguration n) :
    let _sourceTopology : TopologicalSpace
        (CelestialUnorderedConfiguration n) :=
      celestialUnorderedConfigurationTopology n
    @FundamentalGroup
        (CelestialUnorderedConfiguration n)
        (celestialUnorderedConfigurationTopology n) p →*
      End ((celestialConfigurationCoveringLocalSystem R n).obj
        (FundamentalGroupoid.mk p)) := by
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  exact (celestialConfigurationCoveringLocalSystem R n).mapEnd
    (FundamentalGroupoid.mk p)

def celestialConfigurationCoveringLinearMonodromy
    (R : Type*) [Ring R] (n : ℕ)
    (p : CelestialUnorderedConfiguration n) :
    let _sourceTopology : TopologicalSpace
        (CelestialUnorderedConfiguration n) :=
      celestialUnorderedConfigurationTopology n
    @FundamentalGroup
        (CelestialUnorderedConfiguration n)
        (celestialUnorderedConfigurationTopology n) p →*
      LinearMap.GeneralLinearGroup R
        ((celestialConfigurationCoveringLocalSystem R n).obj
          (FundamentalGroupoid.mk p)) := by
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  exact ((moduleCatEndToLinearEnd
      ((celestialConfigurationCoveringLocalSystem R n).obj
        (FundamentalGroupoid.mk p))).comp
    (celestialConfigurationCoveringMonodromy R n p)).toHomUnits

@[simp] theorem celestialConfigurationCoveringLocalSystem_monodromy_single
    (R : Type*) [Ring R] (n : ℕ)
    (p : CelestialUnorderedConfiguration n)
    (gamma : @FundamentalGroup
      (CelestialUnorderedConfiguration n)
      (celestialUnorderedConfigurationTopology n) p)
    (q : {e : CelestialOrderedConfiguration n //
      Quotient.mk' e = p}) (a : R) :
    let _sourceTopology : TopologicalSpace
        (CelestialUnorderedConfiguration n) :=
      celestialUnorderedConfigurationTopology n
    let L := celestialConfigurationCoveringLocalSystem R n
    ((celestialConfigurationCoveringLinearMonodromy R n p gamma :
      LinearMap.GeneralLinearGroup R (L.obj (FundamentalGroupoid.mk p))) :
      Module.End R (L.obj (FundamentalGroupoid.mk p)))
        (Finsupp.single q a) =
      Finsupp.single
        ((@coveringMonodromyPathEquiv
          (CelestialOrderedConfiguration n)
          (CelestialUnorderedConfiguration n)
          (celestialOrderedConfigurationTopology n)
          (celestialUnorderedConfigurationTopology n)
          (@Quotient.mk' (CelestialOrderedConfiguration n)
            (celestialReindexSetoid n))
          (celestialConfigurationCoveringIsCoveringMap n)
          p p
          gamma) q) a := by
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  dsimp only
  change (Finsupp.domLCongr (R := R) (M := R)
    (@coveringMonodromyPathEquiv
      (CelestialOrderedConfiguration n)
      (CelestialUnorderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      (celestialUnorderedConfigurationTopology n)
      (@Quotient.mk' (CelestialOrderedConfiguration n)
        (celestialReindexSetoid n))
      (celestialConfigurationCoveringIsCoveringMap n)
      p p
      gamma)) (Finsupp.single q a) = _
  rw [Finsupp.domLCongr_single]

end InfoGeometry.Twistor.Cl55CelestialConfigurationCoveringLocalSystem
