import InfoGeometry.Clifford.NeutralPhaseSpaceCore

/-!
# Polarized response on the neutral phase-space carrier

This file records only the algebraic compatibility needed for a polarized
response form. It does not assert positivity, Fisher geometry, a Hessian
interpretation, or a metriplectic structure.
-/

namespace InfoGeometry.Canonical.NeutralPhaseSpacePolarizedResponseBridge

open InfoGeometry.Clifford.NeutralPhaseSpaceCore

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

abbrev End (E : Type*) [AddCommGroup E] [Module ℝ E] :=
  PhaseSpaceCarrier E →ₗ[ℝ] PhaseSpaceCarrier E

noncomputable def polarizedForm
    (J L : End E) : PhaseSpaceCarrier E → PhaseSpaceCarrier E → ℝ :=
  fun X Y => canonicalNeutralBilin (J (L X)) Y

def EtaSelfAdjoint (L : End E) : Prop :=
  ∀ X Y, canonicalNeutralBilin (L X) Y = canonicalNeutralBilin X (L Y)

def CommutesWith (J L : End E) : Prop :=
  ∀ X, J (L X) = L (J X)

def HasPolarizedDissipation
    (J L : End E) : Prop :=
  ∀ X, 0 ≤ polarizedForm J L X X

theorem polarizedForm_response_selfAdjoint
    (J L : End E)
    (hL : EtaSelfAdjoint L)
    (hJL : CommutesWith J L)
    (X Y : PhaseSpaceCarrier E) :
    polarizedForm J L X Y = canonicalNeutralBilin (J X) (L Y) := by
  unfold polarizedForm
  rw [hJL X]
  exact hL (J X) Y

end InfoGeometry.Canonical.NeutralPhaseSpacePolarizedResponseBridge
