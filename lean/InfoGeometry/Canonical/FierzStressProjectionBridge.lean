import InfoGeometry.Quantum.Fierz
import InfoGeometry.Algebra.FiniteSpinAlgebra
import InfoGeometry.Canonical.OperatorialHessianBridge
import InfoGeometry.Meta.Architecture

set_option linter.unusedSectionVars false

/-!
# InfoGeometry.Canonical.FierzStressProjectionBridge

Projection bridge from the operatorial Hessian/BKM proxy to a Fierz
stress-tensor readout.

This file deliberately does not assert that linearized gravity has already
been derived from the BKM Hessian.  It states the precise missing bridge:
a concrete model must provide a spin-2 projector, a map from projected
operators to doubled Fierz states, and a stress readout compatible with the
Fierz Hilbert channel.  Under those hypotheses, the BKM/double-commutator
Hessian has a stress projection and the projected stress obeys the Fierz
channel identity.
-/

namespace InfoGeometry.Canonical.FierzStressProjectionBridge

open InfoGeometry.Canonical.BogoliubovTransport
open InfoGeometry.Quantum.Fierz
open InfoGeometry.Canonical.OperatorialHessianBridge
open InfoGeometry.Krein

section Bridge

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

/--
Proof-carrying Fierz projection context for the stress-tensor shadow of the
operatorial Hessian.

`spin2Projector` is intentionally supplied as data.  The repo does not yet
derive the physical spin-2 projection from Clifford/Fierz completeness; this
context records exactly what must be provided before the Hessian may be read as
a stress-tensor channel.
-/
@[rep_depth transport]
structure FierzStressProjectionContext where
  /-- Candidate spin-2 projection on operator Hessian responses. -/
  spin2Projector : EndH → EndH
  /-- State readout used to evaluate Fierz channels after projection. -/
  projectedFierzState : EndH → H₂
  /-- Stress-tensor scalar readout on projected operator responses. -/
  stressTensorReadout : EndH → ℝ
  /-- The spin-2 projection is a projector on the operator lane. -/
  spin2Projector_idempotent :
    ∀ B : EndH, spin2Projector (spin2Projector B) = spin2Projector B
  /--
  Compatibility gate: projected stress equals the Hilbert/Fierz channel of the
  projected operator's associated doubled state.
  -/
  stress_eq_fierzHilbert :
    ∀ B : EndH,
      stressTensorReadout (spin2Projector B) =
        infoHilbert (E := E) (projectedFierzState (spin2Projector B))

namespace FierzStressProjectionContext

variable (C : FierzStressProjectionContext (E := E))

/-- Projected stress readout of an arbitrary operator response. -/
@[rep_depth transport]
def projectedStressReadout (B : EndH) : ℝ :=
  C.stressTensorReadout (C.spin2Projector B)

/-- Projected Fierz state of an arbitrary operator response. -/
@[rep_depth transport]
def projectedState (B : EndH) : H₂ :=
  C.projectedFierzState (C.spin2Projector B)

/-- The projected stress readout is invariant under a second projection. -/
@[rep_depth transport]
theorem projectedStressReadout_projected (B : EndH) :
    C.projectedStressReadout (C.spin2Projector B) =
      C.projectedStressReadout B := by
  simp [projectedStressReadout, C.spin2Projector_idempotent B]

/-- The projected stress readout is the Hilbert/Fierz channel by compatibility. -/
@[rep_depth transport]
theorem projectedStressReadout_eq_fierzHilbert (B : EndH) :
    C.projectedStressReadout B = infoHilbert (E := E) (C.projectedState B) := by
  exact C.stress_eq_fierzHilbert B

/--
Stress readout of the operatorial Hessian/BKM proxy.

This is the conservative Lean form of the Fierz stress projection claim:
the equality holds only after the explicit projection/readout compatibility
context is supplied.
-/
@[rep_depth transport]
theorem operatorInformationHessian_projectedStress_eq_fierzHilbert
    (X A : EndH) :
    C.projectedStressReadout (operatorInformationHessian (E := E) X A) =
      infoHilbert (E := E)
        (C.projectedState (operatorInformationHessian (E := E) X A)) :=
  C.projectedStressReadout_eq_fierzHilbert
    (operatorInformationHessian (E := E) X A)

/--
The same stress readout through the double transport-commutator presentation
of the BKM proxy.
-/
@[rep_depth transport]
theorem doubleTransportCommutator_projectedStress_eq_fierzHilbert
    (X A : EndH) :
    C.projectedStressReadout
        (transportCommutator X (transportCommutator X A)) =
      infoHilbert (E := E)
        (C.projectedState
          (transportCommutator X (transportCommutator X A))) := by
  exact C.projectedStressReadout_eq_fierzHilbert
    (transportCommutator X (transportCommutator X A))

/--
Fierz channel identity for the stress projection of the operatorial Hessian.

This is the current spin-2/stress theorem surface: the squared projected
stress decomposes into scalar, symplectic, and area Fierz channels of the
projected Hessian state.  It is not a global linearized-gravity theorem.
-/
@[rep_depth transport]
theorem operatorInformationHessian_projectedStress_fierz_identity
    (X A : EndH) :
    (C.projectedStressReadout (operatorInformationHessian (E := E) X A)) ^ (2 : ℕ) =
      (infoScalar (E := E)
        (C.projectedState (operatorInformationHessian (E := E) X A))) ^ (2 : ℕ)
        + (infoSymplectic (E := E)
          (C.projectedState (operatorInformationHessian (E := E) X A))) ^ (2 : ℕ)
        + 4 *
          infoArea (E := E)
            (C.projectedState (operatorInformationHessian (E := E) X A)) := by
  rw [C.operatorInformationHessian_projectedStress_eq_fierzHilbert X A]
  exact information_fierz_identity
    (E := E) (C.projectedState (operatorInformationHessian (E := E) X A))

/--
Majorana/zero-area specialization of the projected stress identity.

If the projected Hessian state lies on the Majorana Fierz shadow, the area term
vanishes and the projected stress square is the scalar-plus-symplectic channel
sum.
-/
@[rep_depth transport]
theorem operatorInformationHessian_projectedStress_majorana_identity
    (X A : EndH)
    (hMajorana :
      IsMajoranaBelief
        (E := E) (C.projectedState (operatorInformationHessian (E := E) X A))) :
    (C.projectedStressReadout (operatorInformationHessian (E := E) X A)) ^ (2 : ℕ) =
      (infoScalar (E := E)
        (C.projectedState (operatorInformationHessian (E := E) X A))) ^ (2 : ℕ)
        + (infoSymplectic (E := E)
          (C.projectedState (operatorInformationHessian (E := E) X A))) ^ (2 : ℕ) := by
  rw [C.operatorInformationHessian_projectedStress_eq_fierzHilbert X A]
  exact information_fierz_majorana
    (E := E) (C.projectedState (operatorInformationHessian (E := E) X A))
    hMajorana

end FierzStressProjectionContext

end Bridge

end InfoGeometry.Canonical.FierzStressProjectionBridge
