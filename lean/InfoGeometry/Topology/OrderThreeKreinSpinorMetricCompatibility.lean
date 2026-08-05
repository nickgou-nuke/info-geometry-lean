import InfoGeometry.Krein.KreinSpace
import InfoGeometry.Topology.OrderThreeInvariantMetricAction

/-!
# Krein-spinor compatibility for an order-three metric action

The ordinary orbit cost is only a coarse pseudometric candidate.  This owner
records the additional operator-valued data needed for a Krein/spinor metric
readout: a covariant spinor embedding and a Krein-isometric transport.  It
proves invariance of the induced bilinear and quadratic kernels, but does not
pretend that an indefinite quadratic form is automatically a metric.
-/

noncomputable section

namespace InfoGeometry.Topology.OrderThreeKreinSpinorMetricCompatibility

open InfoGeometry.Krein
open InfoGeometry.Topology.OrderThreeInvariantMetricAction

variable {X H : Type*}
variable [PseudoMetricSpace X]
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [CompleteSpace H] [KreinSpace H]

structure Data where
  actionData : OrderThreeInvariantMetricAction.Data X
  spinor : X → H
  transport : H →L[ℝ] H
  transport_isKreinIsometry : KreinSpace.IsKreinIsometry transport
  transport_commutes_fundamental_symmetry :
    transport.comp (KreinSpace.jCLM (H := H)) =
      (KreinSpace.jCLM (H := H)).comp transport
  spinor_covariant : ∀ x,
    spinor (actionData.action x) = transport (spinor x)

variable (D : Data (X := X) (H := H))

/-- The spinor bilinear kernel read from the Krein pairing. -/
def spinorBilinearKernel (x y : X) : ℝ :=
  KreinSpace.kreinInner (D.spinor x) (D.spinor y)

/-- The diagonal quadratic kernel, kept signed because the Krein form is indefinite. -/
def spinorQuadraticKernel (x : X) : ℝ :=
  spinorBilinearKernel D x x

/-- The squared-difference readout before any positivity or metric claim. -/
def spinorDifferenceKernel (x y : X) : ℝ :=
  KreinSpace.kreinInner (D.spinor x - D.spinor y) (D.spinor x - D.spinor y)

/-- Positive metric candidate obtained by conjugating the Krein product by `J`. -/
def conjugatedPositiveKernel (x y : X) : ℝ :=
  KreinSpace.kreinInner
    (KreinSpace.jCLM (H := H) (D.spinor x - D.spinor y))
    (D.spinor x - D.spinor y)

theorem spinorBilinearKernel_action_invariant (x y : X) :
    spinorBilinearKernel D (D.actionData.action x) (D.actionData.action y) =
      spinorBilinearKernel D x y := by
  change KreinSpace.kreinInner (D.spinor (D.actionData.action x))
      (D.spinor (D.actionData.action y)) =
    KreinSpace.kreinInner (D.spinor x) (D.spinor y)
  rw [D.spinor_covariant, D.spinor_covariant]
  exact D.transport_isKreinIsometry _ _

theorem spinorQuadraticKernel_action_invariant (x : X) :
    spinorQuadraticKernel D (D.actionData.action x) =
      spinorQuadraticKernel D x := by
  exact spinorBilinearKernel_action_invariant D x x

theorem spinorDifferenceKernel_action_invariant (x y : X) :
    spinorDifferenceKernel D (D.actionData.action x) (D.actionData.action y) =
      spinorDifferenceKernel D x y := by
  unfold spinorDifferenceKernel
  rw [D.spinor_covariant, D.spinor_covariant]
  rw [← map_sub]
  exact D.transport_isKreinIsometry _ _

theorem conjugatedPositiveKernel_eq_norm_sq (x y : X) :
    conjugatedPositiveKernel D x y = ‖D.spinor x - D.spinor y‖ ^ 2 := by
  unfold conjugatedPositiveKernel
  simp [KreinSpace.kreinInner_def, KreinSpace.jCLM_apply,
    KreinSpace.J_invol, inner_self_eq_norm_sq]

theorem conjugatedPositiveKernel_nonneg (x y : X) :
    0 ≤ conjugatedPositiveKernel D x y := by
  rw [conjugatedPositiveKernel_eq_norm_sq D]
  exact sq_nonneg _

theorem conjugatedPositiveKernel_action_invariant (x y : X) :
    conjugatedPositiveKernel D (D.actionData.action x) (D.actionData.action y) =
      conjugatedPositiveKernel D x y := by
  let d : H := D.spinor x - D.spinor y
  calc
    conjugatedPositiveKernel D (D.actionData.action x) (D.actionData.action y) =
        KreinSpace.kreinInner
          (KreinSpace.jCLM (H := H) (D.transport d))
          (D.transport d) := by
            simp [conjugatedPositiveKernel, d, D.spinor_covariant]
    _ = KreinSpace.kreinInner
          (D.transport (KreinSpace.jCLM (H := H) d))
          (D.transport d) := by
            rw [← ContinuousLinearMap.comp_apply,
              ← ContinuousLinearMap.comp_apply,
              D.transport_commutes_fundamental_symmetry]
    _ = KreinSpace.kreinInner
          (KreinSpace.jCLM (H := H) d) d := by
            exact D.transport_isKreinIsometry _ _
    _ = conjugatedPositiveKernel D x y := by
      rfl

/-- The Krein adjoint is the correct conjugated-product witness. -/
theorem transport_pairing_via_kreinAdjoint (u v : H) :
    KreinSpace.kreinInner (D.transport u) v =
      KreinSpace.kreinInner u (KreinSpace.kreinAdjoint D.transport v) := by
  exact KreinSpace.kreinInner_kreinAdjoint D.transport u v

theorem transport_preserves_quadratic (u : H) :
    KreinSpace.kreinInner (D.transport u) (D.transport u) =
      KreinSpace.kreinInner u u := by
  exact D.transport_isKreinIsometry u u

end InfoGeometry.Topology.OrderThreeKreinSpinorMetricCompatibility

end
