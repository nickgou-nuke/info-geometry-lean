import InfoGeometry.Twistor.Cl55CelestialOrderedExchangeMonodromy
import InfoGeometry.Twistor.Cl55CelestialLocalSystemMonodromy
import InfoGeometry.Twistor.ProjectiveNullFundamentalGroupRegularMonodromy
import InfoGeometry.Twistor.ProjectiveNullFundamentalGroupRegularLocalSystem

/-!
# Faithful based monodromy of the celestial unordered configuration space

The actual fundamental group of the celestial unordered configuration space
acts by its left-regular representation.  An explicit ordered exchange loop
therefore acts by left multiplication by its genuine based homotopy class.

Unlike deck permutation monodromy, this representation retains pure-loop
information.  It is nevertheless only the canonical based regular
representation: no Yang--Baxter, conformal-block, or anyon identification is
asserted.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55CelestialFundamentalGroupRegularMonodromy

open CategoryTheory
open InfoGeometry.Twistor.Cl55CelestialOrderedExchangeMonodromy
open InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding
open InfoGeometry.Twistor.Cl55CelestialLocalSystemMonodromy
open InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration
open InfoGeometry.Twistor.ProjectiveNullFundamentalGroupRegularLocalSystem
open InfoGeometry.Twistor.ProjectiveNullFundamentalGroupRegularMonodromy
open InfoGeometry.Twistor.ProjectiveNullConfigurationLocalSystemMonodromy

variable (R : Type*) [Semiring R]

/-- The free module on the actual celestial unordered-configuration
fundamental group. -/
abbrev CelestialFundamentalGroupRegularModule
    (n : ℕ) (p : CelestialOrderedConfiguration n) :=
  GroupRegularModule R
    (@FundamentalGroup
      (CelestialUnorderedConfiguration n)
      (celestialUnorderedConfigurationTopology n) (Quotient.mk' p))

/-- Faithful left-regular monodromy of the actual celestial based fundamental
group. -/
def celestialFundamentalGroupRegularMonodromy
    (n : ℕ) (p : CelestialOrderedConfiguration n) :
    @FundamentalGroup
        (CelestialUnorderedConfiguration n)
        (celestialUnorderedConfigurationTopology n) (Quotient.mk' p) →*
      LinearMap.GeneralLinearGroup R
        (CelestialFundamentalGroupRegularModule R n p) := by
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  exact fundamentalGroupRegularMonodromy R
    (CelestialUnorderedConfiguration n) (Quotient.mk' p)

/-- A supplied celestial ordered exchange acts by left multiplication by its
actual unordered based loop class. -/
@[simp] theorem celestialFundamentalGroupRegularMonodromy_orderedExchange
    (n : ℕ) (p : CelestialOrderedConfiguration n)
    (sigma : Equiv.Perm (Fin n))
    (gamma : @Path
      (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      p (celestialPermute n sigma p))
    (delta : @FundamentalGroup
      (CelestialUnorderedConfiguration n)
      (celestialUnorderedConfigurationTopology n) (Quotient.mk' p))
    (r : R) :
    (celestialFundamentalGroupRegularMonodromy R n p
        (celestialOrderedExchangeLoopClass n p sigma gamma) :
      CelestialFundamentalGroupRegularModule R n p →ₗ[R]
        CelestialFundamentalGroupRegularModule R n p)
        (Finsupp.single delta r) =
      Finsupp.single
        (celestialOrderedExchangeLoopClass n p sigma gamma * delta) r := by
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  exact fundamentalGroupRegularMonodromy_single R _ _ _ delta r

theorem celestialFundamentalGroupRegularMonodromy_injective
    [Nontrivial R] (n : ℕ) (p : CelestialOrderedConfiguration n) :
    Function.Injective (celestialFundamentalGroupRegularMonodromy R n p) := by
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  exact fundamentalGroupRegularMonodromy_injective R _ _

section LocalSystem

variable (S : Type*) [Ring S]

/-- The genuine path-torsor local system on the celestial unordered
configuration space, based at the selected ordered configuration. -/
def celestialPathRegularLocalSystem
    (n : ℕ) (p : CelestialOrderedConfiguration n) :
    CelestialConfigurationLocalSystem S n := by
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  exact basedPathRegularLocalSystem S
    (CelestialUnorderedConfiguration n) (Quotient.mk' p)

/-- GL-valued monodromy extracted from the concrete celestial path-torsor
local system. -/
def celestialPathRegularLinearMonodromy
    (n : ℕ) (p : CelestialOrderedConfiguration n) :
    @FundamentalGroup
        (CelestialUnorderedConfiguration n)
        (celestialUnorderedConfigurationTopology n) (Quotient.mk' p) →*
      LinearMap.GeneralLinearGroup S
        (CelestialFundamentalGroupRegularModule S n p) := by
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  let L := celestialPathRegularLocalSystem S n p
  exact ((moduleCatEndToLinearEnd
      (L.obj (FundamentalGroupoid.mk (Quotient.mk' p)))).comp
    (L.mapEnd (FundamentalGroupoid.mk (Quotient.mk' p)))).toHomUnits

/-- The monodromy extracted from the celestial path-torsor local system is
the faithful regular monodromy already exposed above. -/
theorem celestialPathRegularLocalSystem_monodromy_eq
    (n : ℕ) (p : CelestialOrderedConfiguration n) :
    celestialPathRegularLinearMonodromy S n p =
      celestialFundamentalGroupRegularMonodromy S n p := by
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  change basedPathRegularLinearMonodromy S
      (CelestialUnorderedConfiguration n) (Quotient.mk' p) = _
  exact basedPathRegularLinearMonodromy_eq_regular S _ _

/-- The monodromy extracted from the celestial path-torsor local system sends
an explicit exchange basis vector by its actual based loop class. -/
@[simp] theorem celestialPathRegularLinearMonodromy_orderedExchange
    (n : ℕ) (p : CelestialOrderedConfiguration n)
    (sigma : Equiv.Perm (Fin n))
    (gamma : @Path
      (CelestialOrderedConfiguration n)
      (celestialOrderedConfigurationTopology n)
      p (celestialPermute n sigma p))
    (delta : @FundamentalGroup
      (CelestialUnorderedConfiguration n)
      (celestialUnorderedConfigurationTopology n) (Quotient.mk' p))
    (r : S) :
    (celestialPathRegularLinearMonodromy S n p
        (celestialOrderedExchangeLoopClass n p sigma gamma) :
      CelestialFundamentalGroupRegularModule S n p →ₗ[S]
        CelestialFundamentalGroupRegularModule S n p)
        (Finsupp.single delta r) =
      Finsupp.single
        (celestialOrderedExchangeLoopClass n p sigma gamma * delta) r := by
  rw [celestialPathRegularLocalSystem_monodromy_eq]
  exact celestialFundamentalGroupRegularMonodromy_orderedExchange
    S n p sigma gamma delta r

end LocalSystem

end InfoGeometry.Twistor.Cl55CelestialFundamentalGroupRegularMonodromy
