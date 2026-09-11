import InfoGeometry.Canonical.BogoliubovVielbein
import InfoGeometry.Algebra.FiniteSpinAlgebra

noncomputable section

/-!
# Bogoliubov transport of an existing operator basis

This owner transports a supplied basis by `expTransport`; it deliberately does
not redefine the basis or identify the transported operator with a metric.
-/

namespace InfoGeometry.Canonical.BogoliubovBasisConjugation

open InfoGeometry.Canonical.BogoliubovVielbein
open InfoGeometry.Canonical.BogoliubovVielbein.BogoliubovVielbeinBundle
open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Krein

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [CompleteSpace E]

local notation "EndH" => DoubledSpace E →L[ℝ] DoubledSpace E

/-- Conjugation/parallel transport of a supplied vielbein-basis operator. -/
noncomputable def transportedBasis
    (V : BogoliubovVielbeinBundle (E := E))
    (B : ι → EndH) (a : ι) (η : ℝ) : EndH :=
  InfoGeometry.Canonical.expTransport (A := EndH)
    V.connectionGenerator (B a) η

/-- The infinitesimal basis deformation is the connection commutator. -/
theorem deriv_transportedBasis_at_zero
    (V : BogoliubovVielbeinBundle (E := E))
    (B : ι → EndH) (a : ι) :
    deriv (fun η => transportedBasis V B a η) 0 =
      transportCommutator (E := E) V.connectionGenerator (B a) := by
  simpa [transportedBasis] using
    (InfoGeometry.Canonical.deriv_expTransport_at_zero
      (A := EndH) (X := V.connectionGenerator) (A₀ := B a))

/-- The transported basis satisfies the commutator evolution law at every
rapidity, not only infinitesimally at the origin. -/
theorem hasDerivAt_transportedBasis
    (V : BogoliubovVielbeinBundle (E := E))
    (B : ι → EndH) (a : ι) (η : ℝ) :
    HasDerivAt (fun s => transportedBasis V B a s)
      (transportCommutator (E := E) V.connectionGenerator
        (transportedBasis V B a η)) η := by
  change HasDerivAt
    (fun s => InfoGeometry.Canonical.expTransport
      (A := EndH) V.connectionGenerator (B a) s)
    (transportCommutator (E := E) V.connectionGenerator
      (InfoGeometry.Canonical.expTransport
        (A := EndH) V.connectionGenerator (B a) η)) η
  rw [transportCommutator_expTransport (E := E)
    V.connectionGenerator (B a) η]
  exact InfoGeometry.Canonical.hasDerivAt_expTransport
    (A := EndH) (X := V.connectionGenerator) (A₀ := B a) η

end InfoGeometry.Canonical.BogoliubovBasisConjugation
