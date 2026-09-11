import InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional
import InfoGeometry.Algebra.FiniteSpinAlgebra

/-!
# Inner invariance of the algebraic trace

The normalized trace on the raw matrix direct limit is cyclic.  Consequently
it is invariant under conjugation by a unit of the colimit carrier.  This is
the algebraic modular-invariance statement used here; no Gibbs density,
completion, or analytic KMS extension is inferred.
-/

noncomputable section

namespace InfoGeometry.Canonical.CuntzMatrixTraceModularInvariance

open InfoGeometry.Canonical.CuntzMatrixAlgebraicStarColimit
open InfoGeometry.Canonical.CuntzMatrixAlgebraicTraceFunctional

def unitConjugation (u : Carrierˣ) (x : Carrier) : Carrier :=
  (u : Carrier) * x * ((u⁻¹ : Carrierˣ) : Carrier)

@[simp] theorem unitConjugation_apply (u : Carrierˣ) (x : Carrier) :
    unitConjugation u x = (u : Carrier) * x * ((u⁻¹ : Carrierˣ) : Carrier) :=
  rfl

theorem traceFunctional_unitConjugation (u : Carrierˣ) (x : Carrier) :
    traceFunctional (unitConjugation u x) = traceFunctional x := by
  unfold unitConjugation
  rw [traceFunctional_cyclic]
  rw [← mul_assoc]
  rw [show ((u⁻¹ : Carrierˣ) : Carrier) * (u : Carrier) = 1 by
    exact Units.inv_mul u]
  simp

end InfoGeometry.Canonical.CuntzMatrixTraceModularInvariance
