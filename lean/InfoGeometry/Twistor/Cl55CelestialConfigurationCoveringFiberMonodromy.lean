import InfoGeometry.Twistor.Cl55CelestialConfigurationCoveringFiberLinear
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.Cl55CelestialConfigurationCoveringLocalSystem
import InfoGeometry.Twistor.ProjectiveNullConfigurationDeckMonodromy

/-!
# Permutation-labelled monodromy of the direct celestial covering

The direct celestial ordered-to-unordered covering has a finite fiber whose
canonical labels are `Equiv.Perm (Fin n)`.  This owner exposes the covering
monodromy on that fiber and gives its linearized basis readout under the
canonical fiber equivalence.

This is a covering/local-system theorem only.  It does not identify the
fundamental group with a braid group and makes no conformal-block or anyon
claim.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55CelestialConfigurationCoveringFiberMonodromy

open CategoryTheory
open InfoGeometry.Twistor.Cl55CelestialConfigurationCovering
open InfoGeometry.Twistor.Cl55CelestialConfigurationCoveringFiberLinear
open InfoGeometry.Twistor.Cl55CelestialConfigurationCoveringLocalSystem
open InfoGeometry.Twistor.Cl55CelestialConfigurationFiberEquiv
open InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding
open InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationCoveringLocalSystem
open InfoGeometry.Twistor.ProjectiveNullConfigurationDeckMonodromy

variable {R : Type*} [Ring R]

/-- The actual covering monodromy permutation on a direct celestial fiber. -/
noncomputable def celestialConfigurationFiberMonodromy
    (n : ℕ) (p : CelestialOrderedConfiguration n) :
    @FundamentalGroup
        (CelestialUnorderedConfiguration n)
        (celestialUnorderedConfigurationTopology n) (Quotient.mk' p) →*
      Equiv.Perm
        {q : CelestialOrderedConfiguration n //
          Quotient.mk' q = (Quotient.mk' p : CelestialUnorderedConfiguration n)} := by
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  exact coveringMonodromyRepresentation
    (celestialUnorderedProjection_isQuotientCoveringMap n).isCoveringMap
    (Quotient.mk' p)

@[simp] theorem celestialConfigurationFiberMonodromy_apply
    (n : ℕ) (p : CelestialOrderedConfiguration n)
    (gamma : @FundamentalGroup
      (CelestialUnorderedConfiguration n)
      (celestialUnorderedConfigurationTopology n) (Quotient.mk' p))
    (q : {r : CelestialOrderedConfiguration n //
      Quotient.mk' r = (Quotient.mk' p : CelestialUnorderedConfiguration n)}) :
    celestialConfigurationFiberMonodromy n p gamma q =
      (@coveringMonodromyPathEquiv
        (CelestialOrderedConfiguration n)
        (CelestialUnorderedConfiguration n)
        (celestialOrderedConfigurationTopology n)
        (celestialUnorderedConfigurationTopology n)
        (@Quotient.mk' (CelestialOrderedConfiguration n)
          (celestialReindexSetoid n))
        (celestialConfigurationCoveringIsCoveringMap n)
      (Quotient.mk' p) (Quotient.mk' p) gamma) q := by
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  change (coveringMonodromyEquiv
      (celestialConfigurationCoveringIsCoveringMap n)
      gamma) q = _
  rfl

/-! ## Canonical linear fibre readout -/

/-- The covering monodromy transported to the canonical permutation-label
module.  This is the operator-level version of the fibre basis readout. -/
noncomputable def celestialConfigurationCoveringFiberLinearMonodromy
    (R : Type*) [Ring R] (n : ℕ)
    (p : CelestialOrderedConfiguration n)
    (gamma : @FundamentalGroup
      (CelestialUnorderedConfiguration n)
      (celestialUnorderedConfigurationTopology n) (Quotient.mk' p)) :
    Module.End R (DeckPermutationModule R n) :=
  (celestialConfigurationCoveringFiberLinearEquiv R n p).toLinearMap.comp
    ((celestialConfigurationCoveringMonodromy R n
      (Quotient.mk' p) gamma).hom.comp
      (celestialConfigurationCoveringFiberLinearEquiv R n p).symm.toLinearMap)

theorem celestialConfigurationCoveringFiberLinearMonodromy_intertwines
    (R : Type*) [Ring R] (n : ℕ)
    (p : CelestialOrderedConfiguration n)
    (gamma : @FundamentalGroup
      (CelestialUnorderedConfiguration n)
      (celestialUnorderedConfigurationTopology n) (Quotient.mk' p))
    (x : ({q : CelestialOrderedConfiguration n //
      Quotient.mk' q = (Quotient.mk' p : CelestialUnorderedConfiguration n)} →₀ R)) :
    celestialConfigurationCoveringFiberLinearEquiv R n p
        ((celestialConfigurationCoveringMonodromy R n
          (Quotient.mk' p) gamma).hom x) =
      celestialConfigurationCoveringFiberLinearMonodromy R n p gamma
        (celestialConfigurationCoveringFiberLinearEquiv R n p x) := by
  let e := celestialConfigurationCoveringFiberLinearEquiv R n p
  change e ((celestialConfigurationCoveringMonodromy R n
      (Quotient.mk' p) gamma).hom x) =
    e ((celestialConfigurationCoveringMonodromy R n
      (Quotient.mk' p) gamma).hom (e.symm (e x)))
  rw [e.symm_apply_apply]

@[simp] theorem celestialConfigurationCoveringLocalSystem_monodromy_label_single
    (R : Type*) [Ring R] (n : ℕ)
    (p : CelestialOrderedConfiguration n)
    (gamma : @FundamentalGroup
      (CelestialUnorderedConfiguration n)
      (celestialUnorderedConfigurationTopology n) (Quotient.mk' p))
    (tau : Equiv.Perm (Fin n)) (a : R) :
    let _sourceTopology : TopologicalSpace
        (CelestialUnorderedConfiguration n) :=
      celestialUnorderedConfigurationTopology n
    let L := celestialConfigurationCoveringLocalSystem R n
    celestialConfigurationCoveringFiberLinearEquiv R n p
        ((celestialConfigurationCoveringLinearMonodromy R n
          (Quotient.mk' p) gamma :
          Module.End R (L.obj (FundamentalGroupoid.mk (Quotient.mk' p))))
          (Finsupp.single (celestialOrderedFiberEquivPerm n p tau) a)) =
      Finsupp.single
        ((celestialOrderedFiberEquivPerm n p).symm
          (celestialConfigurationFiberMonodromy n p gamma
            (celestialOrderedFiberEquivPerm n p tau))) a := by
  letI : TopologicalSpace (CelestialOrderedConfiguration n) :=
    celestialOrderedConfigurationTopology n
  letI : TopologicalSpace (CelestialUnorderedConfiguration n) :=
    celestialUnorderedConfigurationTopology n
  dsimp only
  change (celestialConfigurationCoveringFiberLinearEquiv R n p)
      ((Finsupp.domLCongr (R := R) (M := R)
        (@coveringMonodromyPathEquiv
          (CelestialOrderedConfiguration n)
          (CelestialUnorderedConfiguration n)
          (celestialOrderedConfigurationTopology n)
          (celestialUnorderedConfigurationTopology n)
          (@Quotient.mk' (CelestialOrderedConfiguration n)
            (celestialReindexSetoid n))
          (celestialConfigurationCoveringIsCoveringMap n)
          (Quotient.mk' p) (Quotient.mk' p) gamma))
        (Finsupp.single (celestialOrderedFiberEquivPerm n p tau) a)) = _
  rw [Finsupp.domLCongr_single,
    celestialConfigurationCoveringFiberLinearEquiv_single]
  rw [celestialConfigurationFiberMonodromy_apply]

end InfoGeometry.Twistor.Cl55CelestialConfigurationCoveringFiberMonodromy
