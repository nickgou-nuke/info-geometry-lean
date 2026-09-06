import InfoGeometry.Twistor.Cl55CelestialLocalSystemMonodromy
import InfoGeometry.Twistor.ProjectiveNullOrderedExchangePath

/-!
# Ordered celestial exchange paths and local-system monodromy

An ordered path between a celestial configuration and one of its finite
reindexings descends to an actual based loop in the unordered celestial
configuration space.  The existing celestial local-system pullback then
evaluates this loop by the ambient projective-`Q55` monodromy after the
induced map of fundamental groups.

The ordered path is explicit input.  This owner does not assert a canonical
exchange path, identify a spherical braid group, construct conformal blocks,
or supply anyon fusion data.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55CelestialOrderedExchangeMonodromy

open InfoGeometry.Clifford.Clifford55
open InfoGeometry.Twistor.Cl55CelestialLocalSystemMonodromy
open InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding
open InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration
open InfoGeometry.Twistor.Cl55CelestialUnorderedFundamentalGroup
open InfoGeometry.Twistor.ProjectiveNullConfigurationLocalSystemMonodromy
open InfoGeometry.Twistor.ProjectiveNullConfigurationTopology
open InfoGeometry.Twistor.ProjectiveNullOrderedExchangePath
open InfoGeometry.Twistor.ProjectiveNullUnorderedConfiguration

variable {R : Type*} [Ring R]

/-- An ordered celestial path ending at a finite reindexing descends to a
based loop in the unordered celestial configuration space. -/
def celestialOrderedExchangeLoop
    (n : ℕ) (p : CelestialOrderedConfiguration n)
    (sigma : Equiv.Perm (Fin n))
    (gamma : @Path
      (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      p (celestialPermute n sigma p)) :
    @Path
      (CelestialUnorderedConfiguration n)
      (celestialUnorderedConfigurationTopology n)
      (Quotient.mk' p) (Quotient.mk' p) := by
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  let projected := gamma.map (celestialUnorderedProjection_continuous n)
  have hend : (Quotient.mk' p : CelestialUnorderedConfiguration n) =
      Quotient.mk' (celestialPermute n sigma p) := by
    apply Quotient.sound
    exact (celestialReindexSetoid_iff n p
      (celestialPermute n sigma p)).2 ⟨sigma, rfl⟩
  exact projected.cast rfl hend

@[simp] theorem celestialOrderedExchangeLoop_apply
    (n : ℕ) (p : CelestialOrderedConfiguration n)
    (sigma : Equiv.Perm (Fin n))
    (gamma : @Path
      (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      p (celestialPermute n sigma p)) (t : unitInterval) :
    celestialOrderedExchangeLoop n p sigma gamma t =
      Quotient.mk' (gamma t) := by
  rfl

/-- The based fundamental-group class represented by an explicit ordered
celestial exchange path. -/
def celestialOrderedExchangeLoopClass
    (n : ℕ) (p : CelestialOrderedConfiguration n)
    (sigma : Equiv.Perm (Fin n))
    (gamma : @Path
      (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      p (celestialPermute n sigma p)) :
    @FundamentalGroup
      (CelestialUnorderedConfiguration n)
      (celestialUnorderedConfigurationTopology n)
      (Quotient.mk' p) := by
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  exact Path.Homotopic.Quotient.mk
    (celestialOrderedExchangeLoop n p sigma gamma)

/-- The ambient ordered path obtained by applying the concrete celestial
embedding componentwise. -/
def celestialOrderedExchangeAmbientPath
    (n : ℕ) (p : CelestialOrderedConfiguration n)
    (sigma : Equiv.Perm (Fin n))
    (gamma : @Path
      (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      p (celestialPermute n sigma p)) :
    @Path (Ordered Q55 n) (orderedConfigurationTopology Q55 n)
      (celestialOrderedConfigurationMap n p)
      (permute Q55 n sigma (celestialOrderedConfigurationMap n p)) := by
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  letI : TopologicalSpace (Ordered Q55 n) :=
    orderedConfigurationTopology Q55 n
  let mapped := gamma.map
    (celestialOrderedConfigurationMap_isEmbedding n).continuous
  exact mapped.cast rfl
    (celestialOrderedConfigurationMap_respects_permute n sigma p).symm

@[simp] theorem celestialOrderedExchangeAmbientPath_apply
    (n : ℕ) (p : CelestialOrderedConfiguration n)
    (sigma : Equiv.Perm (Fin n))
    (gamma : @Path
      (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      p (celestialPermute n sigma p)) (t : unitInterval) :
    celestialOrderedExchangeAmbientPath n p sigma gamma t =
      celestialOrderedConfigurationMap n (gamma t) := by
  rfl

/-- The map on fundamental groups induced by the celestial embedding sends
the celestial exchange class to the ambient ordered-exchange class of the
componentwise embedded path. -/
theorem celestialUnorderedFundamentalGroupMap_orderedExchangeLoopClass
    (n : ℕ) (p : CelestialOrderedConfiguration n)
    (sigma : Equiv.Perm (Fin n))
    (gamma : @Path
      (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      p (celestialPermute n sigma p)) :
    celestialUnorderedFundamentalGroupMap n (Quotient.mk' p)
        (celestialOrderedExchangeLoopClass n p sigma gamma) =
      orderedExchangeLoopClass Q55 n
        (celestialOrderedConfigurationMap n p) sigma
        (celestialOrderedExchangeAmbientPath n p sigma gamma) := by
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  letI : TopologicalSpace (Ordered Q55 n) :=
    orderedConfigurationTopology Q55 n
  letI : TopologicalSpace (Unordered Q55 n) :=
    unorderedConfigurationTopology Q55 n
  unfold celestialUnorderedFundamentalGroupMap
  unfold celestialOrderedExchangeLoopClass orderedExchangeLoopClass
  unfold InfoGeometry.Twistor.ProjectiveNullConfigurationExchangeLoop.configurationLoopClass
  apply congrArg Path.Homotopic.Quotient.mk
  apply (Path.ext_iff).2
  funext t
  rfl

/-- Categorical monodromy of an explicit celestial ordered exchange is the
ambient monodromy evaluated after its induced celestial fundamental-group
class. -/
theorem celestialPullbackMonodromy_orderedExchangeLoopClass
    (n : ℕ) (L : ConfigurationLocalSystem R Q55 n)
    (p : CelestialOrderedConfiguration n)
    (sigma : Equiv.Perm (Fin n))
    (gamma : @Path
      (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      p (celestialPermute n sigma p)) :
    let _sourceTopology : TopologicalSpace
        (CelestialUnorderedConfiguration n) :=
      celestialUnorderedConfigurationTopology n
    let _targetTopology : TopologicalSpace (Unordered Q55 n) :=
      unorderedConfigurationTopology Q55 n
    celestialPullbackMonodromy n L (Quotient.mk' p)
        (celestialOrderedExchangeLoopClass n p sigma gamma) =
      localSystemMonodromy Q55 n L
        (Quotient.mk' (celestialOrderedConfigurationMap n p))
        (orderedExchangeLoopClass Q55 n
          (celestialOrderedConfigurationMap n p) sigma
          (celestialOrderedExchangeAmbientPath n p sigma gamma)) := by
  rw [celestialPullbackMonodromy_eq_ambient,
    celestialUnorderedFundamentalGroupMap_orderedExchangeLoopClass]
  rfl

/-- The same exchange readout for the literal general-linear monodromy
representation carried by the pulled-back local system. -/
theorem celestialPullbackLinearMonodromy_orderedExchangeLoopClass
    (n : ℕ) (L : ConfigurationLocalSystem R Q55 n)
    (p : CelestialOrderedConfiguration n)
    (sigma : Equiv.Perm (Fin n))
    (gamma : @Path
      (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      p (celestialPermute n sigma p)) :
    let _sourceTopology : TopologicalSpace
        (CelestialUnorderedConfiguration n) :=
      celestialUnorderedConfigurationTopology n
    let _targetTopology : TopologicalSpace (Unordered Q55 n) :=
      unorderedConfigurationTopology Q55 n
    celestialPullbackLinearMonodromy n L (Quotient.mk' p)
        (celestialOrderedExchangeLoopClass n p sigma gamma) =
      localSystemLinearMonodromy Q55 n L
        (Quotient.mk' (celestialOrderedConfigurationMap n p))
        (orderedExchangeLoopClass Q55 n
          (celestialOrderedConfigurationMap n p) sigma
          (celestialOrderedExchangeAmbientPath n p sigma gamma)) := by
  rw [celestialPullbackLinearMonodromy_eq_ambient,
    celestialUnorderedFundamentalGroupMap_orderedExchangeLoopClass]
  rfl

end InfoGeometry.Twistor.Cl55CelestialOrderedExchangeMonodromy
