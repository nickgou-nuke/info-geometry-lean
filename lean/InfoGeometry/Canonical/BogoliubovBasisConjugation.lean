/-
Copyright (c) 2026 InfoGeometry Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: InfoGeometry Engine Contributors
-/

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

/-- A Bogoliubov vielbein transports a q-Heisenberg relation with its same
parameter and central term. The frame deformation is removed from the
coordinates by conjugation, while the operator algebra itself is unchanged. -/
theorem transportedBasis_preserves_qHeisenberg_relation
    (V : BogoliubovVielbeinBundle (E := E))
    (B : ι → EndH) (i j : ι) (q c η : ℝ)
    (h : B i * B j - q • (B j * B i) = c • (1 : EndH)) :
    transportedBasis V B i η * transportedBasis V B j η -
        q • (transportedBasis V B j η * transportedBasis V B i η) =
      c • (1 : EndH) := by
  simpa [transportedBasis] using
    (InfoGeometry.Canonical.expTransport_preserves_qHeisenberg_relation
      V.connectionGenerator (B i) (B j) q c η h)

/-- The ordinary Heisenberg commutator keeps its central coefficient under
Bogoliubov-vielbein transport. In particular, this conjugation transports the
representation of the relation; it does not remove or renormalize its central
deformation. -/
theorem transportedBasis_preserves_heisenberg_commutator
    (V : BogoliubovVielbeinBundle (E := E))
    (B : ι → EndH) (i j : ι) (c η : ℝ)
    (h : B i * B j - B j * B i = c • (1 : EndH)) :
    transportedBasis V B i η * transportedBasis V B j η -
        transportedBasis V B j η * transportedBasis V B i η =
      c • (1 : EndH) := by
  simpa using transportedBasis_preserves_qHeisenberg_relation
    (V := V) B i j 1 c η (by simpa using h)

/-- The infinitesimal basis deformation is the connection commutator. -/
theorem deriv_transportedBasis_at_zero
    (V : BogoliubovVielbeinBundle (E := E))
    (B : ι → EndH) (a : ι) :
    deriv (fun η => transportedBasis V B a η) 0 =
      transportCommutator (E := E) V.connectionGenerator (B a) := by
  change deriv (fun η => InfoGeometry.Canonical.expTransport
    (A := EndH) V.connectionGenerator (B a) η) 0 =
      transportCommutator (E := E) V.connectionGenerator (B a)
  rw [← lieBracket_eq_transportCommutator (E := E)]
  exact InfoGeometry.Canonical.deriv_expTransport_at_zero
    (A := EndH) (X := V.connectionGenerator) (A₀ := B a)

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
