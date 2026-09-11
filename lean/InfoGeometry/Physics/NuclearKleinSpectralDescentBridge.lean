import Mathlib
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Physics.NuclearKleinParameterBundle
import InfoGeometry.Canonical.D6KleinDiracBands

/-!
# Nuclear effective operators and existing Klein spectral descent

The repository already has real Dirac-band observables on the same finite
Klein quotient used by `NuclearKleinParameterBundle`.  This file records that
common base without identifying the nuclear Schur operator with those bands.

Both sides descend because their cover-level representatives are glide
invariant.  This is a structural common-quotient theorem, not a spectral
identification or eigenvalue-monodromy theorem.
-/

noncomputable section

namespace InfoGeometry.Physics.NuclearKleinSpectralDescentBridge

open InfoGeometry.Canonical.D6HexTiledKleinBottleQuotient
open InfoGeometry.Canonical.D6KleinDiracBands
open InfoGeometry.Physics.NuclearOperatorSuperSoloviev
open InfoGeometry.Physics.NuclearOperatorSchurComplement
open InfoGeometry.Physics.NuclearKleinParameterBundle

variable {A : Type*} [Ring A]
variable {P : InternalParity A}

/-- The nuclear effective operator and both pre-existing Dirac band branches
are ordinary functions on exactly the same finite Klein quotient. -/
structure CommonKleinObservables
    (H : KleinEquivariantHamiltonian P) (R : ResolventData A) where
  nuclearEffective : KleinHexQuotient → A := H.quotientEffectiveOperator R
  diracBandPlus : KleinHexQuotient → ℝ := quotientBandPlus
  diracBandMinus : KleinHexQuotient → ℝ := quotientBandMinus
  diracBandGap : KleinHexQuotient → ℝ := quotientBandGap

/-- Pulling all common quotient observables back to the torus cover recovers
their respective cover-level representatives. -/
theorem common_pullback_packet
    (H : KleinEquivariantHamiltonian P) (R : ResolventData A)
    (p : TorusCell) :
    H.quotientEffectiveOperator R (quotientMap p) = H.effectiveAt R p ∧
      quotientBandPlus (quotientMap p) = bandPlus p ∧
      quotientBandMinus (quotientMap p) = bandMinus p ∧
      quotientBandGap (quotientMap p) = bandGap p := by
  exact ⟨H.quotientEffectiveOperator_mk R p,
    quotientBandPlus_pullback p,
    quotientBandMinus_pullback p,
    quotientBandGap_pullback p⟩

/-- On the cover, both the nuclear effective operator and the existing band
branches are glide invariant. -/
theorem common_glide_invariance_packet
    (H : KleinEquivariantHamiltonian P) (R : ResolventData A)
    (p : TorusCell) :
    H.effectiveAt R (glide p) = H.effectiveAt R p ∧
      bandPlus (glide p) = bandPlus p ∧
      bandMinus (glide p) = bandMinus p := by
  exact ⟨H.effectiveAt_glide R p,
    bandPlus_glide p,
    bandMinus_glide p⟩

/-- The two pre-existing real band branches solve the quotient spectral
polynomial whenever its radicand is nonnegative.  The theorem is re-exposed
here only to make the common Klein base explicit. -/
theorem quotient_band_roots_packet
    (q : KleinHexQuotient) (h : 0 ≤ quotientRadicand q) :
    quotientSpectralPolynomial q (quotientBandPlus q) = 0 ∧
      quotientSpectralPolynomial q (quotientBandMinus q) = 0 :=
  ⟨quotientSpectralPolynomial_bandPlus q h,
    quotientSpectralPolynomial_bandMinus q h⟩

/-- Structural common-base packet.  No equality between nuclear and Dirac
observables is asserted. -/
theorem common_klein_quotient_packet
    (H : KleinEquivariantHamiltonian P) (R : ResolventData A)
    (p : TorusCell) :
    H.quotientEffectiveOperator R (quotientMap p) = H.effectiveAt R p ∧
      H.effectiveAt R (glide p) = H.effectiveAt R p ∧
      quotientBandGap (quotientMap p) = bandGap p ∧
      bandPlus (glide p) = bandPlus p ∧
      bandMinus (glide p) = bandMinus p := by
  exact ⟨H.quotientEffectiveOperator_mk R p,
    H.effectiveAt_glide R p,
    quotientBandGap_pullback p,
    bandPlus_glide p,
    bandMinus_glide p⟩

end InfoGeometry.Physics.NuclearKleinSpectralDescentBridge

end noncomputable section
