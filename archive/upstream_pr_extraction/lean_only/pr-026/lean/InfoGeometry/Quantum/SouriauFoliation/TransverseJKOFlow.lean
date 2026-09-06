/-
InfoGeometry/Quantum/SouriauFoliation/TransverseJKOFlow.lean
-/
import InfoGeometry.Quantum.SouriauFoliation.SymplecticLeaf

noncomputable section

namespace InfoGeometry.Quantum.SouriauFoliation

/--
Witness-gated transverse JKO-style step.

The sidecar does not prescribe what the transverse law is.  A concrete model may
use energy decrease, divergence decrease, entropy increase, or another
projective/Weyl criterion, but it must supply the law explicitly.
-/
structure TransverseJKOFlow
    {State : Type*}
    (L : SymplecticLeaf State) where
  /-- One dissipative step. -/
  step : State → State

  /-- Model-specific transverse law. -/
  transverseLaw : State → State → Prop

  /-- The supplied step satisfies the transverse law from points on the leaf. -/
  step_law :
    ∀ ⦃x : State⦄, x ∈ L.carrier → transverseLaw x (step x)

namespace TransverseJKOFlow

variable {State : Type*}
variable {L : SymplecticLeaf State}
variable (J : TransverseJKOFlow L)

/-- Re-export the supplied transverse law for one JKO-style step. -/
theorem transverse_step
    {x : State}
    (hx : x ∈ L.carrier) :
    J.transverseLaw x (J.step x) :=
  J.step_law hx

end TransverseJKOFlow

end InfoGeometry.Quantum.SouriauFoliation
