/- SPDX-License-Identifier: Apache-2.0 -/

import InfoGeometry.Algebra.Zorn.G2TwoConcreteWeylG2
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.KleinPresentedGroup
import InfoGeometry.Canonical.KleinMonodromyRepresentationSpace

/-!
# Concrete Klein morphism on the `G₂` Weyl carrier

The Klein relation is realized here on the existing concrete Weyl
automorphisms.  The glide is the simple reflection `s` and the monodromy is
the Coxeter element `c`.  This is deliberately a Weyl-quotient statement:
the Artin generators themselves are not asserted to be involutions.
-/

namespace InfoGeometry.Exceptional.G2WeylKleinBridge

open InfoGeometry.Canonical.KleinPresentedGroup
open InfoGeometry.Algebra.Zorn.G2ConcreteWeylG2
open InfoGeometry.OperatorAlgebra.G2TwoAutomorphismTheorem

noncomputable section

/-- The concrete Klein pair `(s,c)` on the existing `G₂` Weyl carrier. -/
def concreteWeylKleinPair :
    InfoGeometry.Canonical.KleinMonodromyRepresentationSpace.KleinMonodromyPair
      SplitOctF2Aut := by
  exact ⟨(s, c), by
    simpa [s_sq] using s_c_s⟩

/-- The concrete morphism from the Klein presentation to the Weyl carrier. -/
def kleinToConcreteWeyl : KleinGroup →* SplitOctF2Aut :=
  kleinRep concreteWeylKleinPair.a concreteWeylKleinPair.b
    concreteWeylKleinPair.relation

@[simp] theorem kleinToConcreteWeyl_genA :
    kleinToConcreteWeyl (toKlein genA) = s := by
  exact (kleinRep_relator_relation concreteWeylKleinPair.a
    concreteWeylKleinPair.b concreteWeylKleinPair.relation).1

@[simp] theorem kleinToConcreteWeyl_genB :
    kleinToConcreteWeyl (toKlein genB) = c := by
  exact (kleinRep_relator_relation concreteWeylKleinPair.a
    concreteWeylKleinPair.b concreteWeylKleinPair.relation).2

theorem g2Weyl_kleinConjugation :
    kleinToConcreteWeyl (toKlein genA) *
        kleinToConcreteWeyl (toKlein genB) *
        (kleinToConcreteWeyl (toKlein genA))⁻¹ =
      (kleinToConcreteWeyl (toKlein genB))⁻¹ := by
  rw [kleinToConcreteWeyl_genA, kleinToConcreteWeyl_genB]
  simpa [s_sq] using s_c_s

end
end InfoGeometry.Exceptional.G2WeylKleinBridge
