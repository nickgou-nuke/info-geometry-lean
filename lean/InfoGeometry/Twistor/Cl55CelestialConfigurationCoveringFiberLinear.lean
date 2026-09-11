import InfoGeometry.Twistor.Cl55CelestialConfigurationFiberEquiv
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Twistor.ProjectiveNullConfigurationPermutationLinearMonodromy

/-!
# Linearized labels of a celestial covering fiber

The finite celestial ordered-to-unordered covering has a canonical fiber
labeling by `Equiv.Perm (Fin n)`.  This owner linearizes that labeling over a
coefficient ring.  It is a fiber readout only: no braid-group or anyon claim
is made here.
-/

noncomputable section

namespace InfoGeometry.Twistor.Cl55CelestialConfigurationCoveringFiberLinear

open InfoGeometry.Twistor.Cl55CelestialConfigurationFiberEquiv
open InfoGeometry.Twistor.Cl55CelestialOrderedConfigurationEmbedding
open InfoGeometry.Twistor.Cl55CelestialUnorderedConfiguration
open InfoGeometry.Twistor.ProjectiveNullConfigurationDeckMonodromy

/-! ## Canonical linear fiber labeling -/

/-- The free module on the ordered celestial fiber is canonically the free
module on its permutation labels. -/
noncomputable def celestialConfigurationCoveringFiberLinearEquiv
    (R : Type*) [Semiring R] (n : ℕ)
    (p : CelestialOrderedConfiguration n) :
    ({q : CelestialOrderedConfiguration n //
        Quotient.mk' q = (Quotient.mk' p : CelestialUnorderedConfiguration n)} →₀ R) ≃ₗ[R]
      DeckPermutationModule R n :=
  Finsupp.domLCongr (R := R) (M := R)
    (celestialOrderedFiberEquivPerm n p).symm

@[simp] theorem celestialConfigurationCoveringFiberLinearEquiv_single
    (R : Type*) [Semiring R] (n : ℕ)
    (p : CelestialOrderedConfiguration n)
    (q : {r : CelestialOrderedConfiguration n //
      Quotient.mk' r = (Quotient.mk' p : CelestialUnorderedConfiguration n)})
    (a : R) :
    celestialConfigurationCoveringFiberLinearEquiv R n p
        (Finsupp.single q a) =
      Finsupp.single ((celestialOrderedFiberEquivPerm n p).symm q) a := by
  exact Finsupp.domLCongr_single (celestialOrderedFiberEquivPerm n p).symm q a

/-- Over a field, the direct celestial covering fiber has dimension `n!`. -/
theorem celestialConfigurationCoveringFiber_finrank
    (F : Type*) [Field F] (n : ℕ)
    (p : CelestialOrderedConfiguration n) :
    Module.finrank F
        ({q : CelestialOrderedConfiguration n //
          Quotient.mk' q = (Quotient.mk' p : CelestialUnorderedConfiguration n)} →₀ F) =
      n.factorial := by
  rw [(celestialConfigurationCoveringFiberLinearEquiv F n p).finrank_eq]
  change Module.finrank F (Equiv.Perm (Fin n) →₀ F) = n.factorial
  rw [Module.finrank_eq_card_basis Finsupp.basisSingleOne]
  simp [Fintype.card_perm]

end InfoGeometry.Twistor.Cl55CelestialConfigurationCoveringFiberLinear
