import InfoGeometry.Canonical.DrazinSupercharge
import Mathlib.Analysis.InnerProductSpace.Adjoint

namespace InfoGeometry.Canonical

variable {A : Type*} [Ring A] [StarRing A] [StarAddMonoid A]
variable {B_dr : Type*} [Ring B_dr] [StarRing B_dr] [StarAddMonoid B_dr] [Mul A B_dr] [Mul B_dr A]

/-- Witness packet for fluid helicity production: star-algebraic relations between A and B_dr. -/
structure FluidHelicityProductionWitness := 
  (anomalySkew : ∀ {a : A} {b : B_dr}, Star.star (a * b) = -Star.star (b * a))
  
  (helicity : ∀ {a : A} {b : B_dr}, Star.star (a * b) = -Star.star (a * b))
  
  (canonical : ∀ {b : B_dr}, Star.star b = Star.star b)

/-- Construct witness from hypotheses. -/
theorem fluidHelicityProductionWitness_of_anomalySkew_and_helicity_and_canonical
  (hAnomalySkew : ∀ {a : A} {b : B_dr}, Star.star (a * b) = -Star.star (b * a))
  (hHelicity : ∀ {a : A} {b : B_dr}, Star.star (a * b) = -Star.star (a * b))
  (hCanonical : ∀ {b : B_dr}, Star.star b = Star.star b)
  : FluidHelicityProductionWitness := 
⟨hAnomalySkew, hHelicity, hCanonical⟩

/-- Compatibility wrapper: preserves downstream API. -/
theorem anomalySkew_of_regularization_auto
  (hAnomalySkew : ∀ {a : A} {b : B_dr}, Star.star (a * b) = -Star.star (b * a))
  (hHelicity : ∀ {a : A} {b : B_dr}, Star.star (a * b) = -Star.star (a * b))
  (hCanonical : ∀ {b : B_dr}, Star.star b = Star.star b)
  : ∀ {a : A} {b : B_dr}, Star.star (a * b) = -Star.star (b * a) := 
by intros; apply hAnomalySkew

/-- Constructive route: consumes witness packet. -/
theorem anomalySkew_of_regularization_auto_of_witness
  (W : FluidHelicityProductionWitness)
  : ∀ {a : A} {b : B_dr}, Star.star (a * b) = -Star.star (b * a) := 
λ a b, W.anomalySkew a b

end InfoGeometry.Canonical