import Mathlib.Tactic
import InfoGeometry.OperatorAlgebra.DrazinEntropyFunctional
import InfoGeometry.GromovWittenErlangen.LieOrbitCurve

/-!
InfoGeometry/OperatorAlgebra/DrazinLaplacianLocalization.lean

Drazin-Laplacian localization layer.

This module implements the next finite stage of the Drazin/Gromov-Witten bridge:

* a model supplies a Laplacian-like operator attached to each state;
* Drazin regularization supplies a stable volume for that operator;
* an Euler-weight readout is calibrated to that stable volume;
* entropy is then `k_B log` of the Euler/Drazin stable weight;
* a GW localization graph can attach these statewise readouts to localization
  edge contributions.

No Hodge theorem, Moore--Penrose theorem, Drazin existence theorem, Euler-class
localization theorem, or Gromov-Witten localization theorem is asserted here.
-/

noncomputable section

namespace InfoGeometry.OperatorAlgebra

/--
Drazin-Laplacian calibration.

`laplacian` is the model-specific operator whose regular/stable Drazin volume
is read as an Euler weight. The equality between the Euler weight and the
stable volume is a supplied calibration, not a derived localization theorem.
-/
structure DrazinLaplacianCalibration (Op State : Type*) [Add Op] [Mul Op] where
  /-- Underlying Drazin entropy functional. -/
  functional : DrazinEntropyFunctional Op State
  /-- Model-specific Laplacian-like operator. -/
  laplacian : State -> Op
  /-- The Laplacian is the operator whose Drazin readout is being used. -/
  laplacian_eq_element :
    ∀ s : State, functional.readout.valid s ->
      laplacian s = functional.readout.elementOf s
  /-- Euler/localization weight read from the Laplacian sector. -/
  eulerWeight : State -> ℝ
  /-- Euler weight equals the Drazin-stable volume on valid states. -/
  eulerWeight_eq_stableVolume :
    ∀ s : State, functional.readout.valid s ->
      eulerWeight s = functional.readout.stableVolume s

namespace DrazinLaplacianCalibration

variable {Op State : Type*} [Add Op] [Mul Op]
variable (C : DrazinLaplacianCalibration Op State)

/-- The Euler weight is positive on valid states. -/
theorem eulerWeight_pos
    (s : State) (hs : C.functional.readout.valid s) :
    0 < C.eulerWeight s := by
  rw [C.eulerWeight_eq_stableVolume s hs]
  exact C.functional.readout.stableVolume_pos s hs

/-- The Euler weight is nonzero on valid states. -/
theorem eulerWeight_ne_zero
    (s : State) (hs : C.functional.readout.valid s) :
    C.eulerWeight s ≠ 0 :=
  (C.eulerWeight_pos s hs).ne'

/-- Entropy expressed through the calibrated Euler/Drazin stable weight. -/
theorem entropy_eq_kB_log_eulerWeight
    (s : State) (hs : C.functional.readout.valid s) :
    C.functional.entropy s =
      C.functional.kB * Real.log (C.eulerWeight s) := by
  calc
    C.functional.entropy s
        = C.functional.kB * Real.log (C.functional.readout.stableVolume s) :=
            C.functional.entropy_eq_kB_log_volume s hs
    _ = C.functional.kB * Real.log (C.eulerWeight s) := by
            rw [C.eulerWeight_eq_stableVolume s hs]

/-- Entropy is nonnegative if the calibrated Euler weight is at least one. -/
theorem entropy_nonneg_of_one_le_eulerWeight
    (s : State) (hs : C.functional.readout.valid s)
    (hweight : 1 ≤ C.eulerWeight s) :
    0 ≤ C.functional.entropy s := by
  rw [C.entropy_eq_kB_log_eulerWeight s hs]
  exact mul_nonneg C.functional.kB_pos.le (Real.log_nonneg hweight)

/-- Entropy is strictly positive if the calibrated Euler weight is greater than one. -/
theorem entropy_pos_of_one_lt_eulerWeight
    (s : State) (hs : C.functional.readout.valid s)
    (hweight : 1 < C.eulerWeight s) :
    0 < C.functional.entropy s := by
  rw [C.entropy_eq_kB_log_eulerWeight s hs]
  exact mul_pos C.functional.kB_pos (Real.log_pos hweight)

end DrazinLaplacianCalibration

end InfoGeometry.OperatorAlgebra

namespace InfoGeometry.GromovWittenErlangen

open InfoGeometry.OperatorAlgebra

/--
GW localization graph with Drazin-Laplacian edge readouts.

Each localization edge is assigned a state for the Drazin-Laplacian calibration.
The edge Euler weight and edge contribution readout are calibrated to the
Drazin entropy of that state.
-/
structure GWDrazinLaplacianBridge
    (G T Target Coeff Op State : Type*) [Add Op] [Mul Op] where
  /-- Underlying finite GW/Erlangen localization packet. -/
  virtualLocalization :
    VirtualLocalizationOrbitPacket G T Target Coeff
  /-- Drazin-Laplacian calibration used on localization sectors. -/
  laplacianCalibration :
    DrazinLaplacianCalibration Op State
  /-- Assign a Drazin-Laplacian state to each localization edge. -/
  edgeState :
    virtualLocalization.graph.Edge -> State
  /-- Assigned edge states are valid for the Drazin-Laplacian calibration. -/
  edgeState_mem_domain :
    ∀ e : virtualLocalization.graph.Edge,
      laplacianCalibration.functional.readout.valid (edgeState e)
  /-- Euler weight supplied by the localization model on each edge. -/
  edgeEulerWeight :
    virtualLocalization.graph.Edge -> ℝ
  /-- Edge Euler weight agrees with the Drazin-Laplacian Euler readout. -/
  edgeEulerWeight_eq_laplacianWeight :
    ∀ e : virtualLocalization.graph.Edge,
      edgeEulerWeight e =
        laplacianCalibration.eulerWeight (edgeState e)
  /-- Scalar readout of edge contribution coefficients. -/
  edgeContributionReadout : Coeff -> ℝ
  /-- Edge contribution readout equals the Drazin entropy of the assigned edge state. -/
  edgeContribution_eq_entropy :
    ∀ e : virtualLocalization.graph.Edge,
      edgeContributionReadout (virtualLocalization.edgeContribution e) =
        laplacianCalibration.functional.entropy (edgeState e)

namespace GWDrazinLaplacianBridge

variable {G T Target Coeff Op State : Type*} [Add Op] [Mul Op]
variable (B : GWDrazinLaplacianBridge G T Target Coeff Op State)

/-- The edge Euler weight is positive. -/
theorem edgeEulerWeight_pos
    (e : B.virtualLocalization.graph.Edge) :
    0 < B.edgeEulerWeight e := by
  rw [B.edgeEulerWeight_eq_laplacianWeight e]
  exact B.laplacianCalibration.eulerWeight_pos (B.edgeState e) (B.edgeState_mem_domain e)

/-- Edge contribution readout as `k_B log` of the calibrated edge Euler weight. -/
theorem edgeContribution_eq_kB_log_edgeEulerWeight
    (e : B.virtualLocalization.graph.Edge) :
    B.edgeContributionReadout (B.virtualLocalization.edgeContribution e) =
      B.laplacianCalibration.functional.kB * Real.log (B.edgeEulerWeight e) := by
  calc
    B.edgeContributionReadout (B.virtualLocalization.edgeContribution e)
        = B.laplacianCalibration.functional.entropy (B.edgeState e) :=
            B.edgeContribution_eq_entropy e
    _ = B.laplacianCalibration.functional.kB *
          Real.log (B.laplacianCalibration.eulerWeight (B.edgeState e)) :=
            B.laplacianCalibration.entropy_eq_kB_log_eulerWeight
              (B.edgeState e) (B.edgeState_mem_domain e)
    _ = B.laplacianCalibration.functional.kB * Real.log (B.edgeEulerWeight e) := by
            rw [B.edgeEulerWeight_eq_laplacianWeight e]

/-- Edge contribution readout is nonnegative when the edge Euler weight is at least one. -/
theorem edgeContribution_nonneg_of_one_le_edgeEulerWeight
    (e : B.virtualLocalization.graph.Edge)
    (hweight : 1 ≤ B.edgeEulerWeight e) :
    0 ≤ B.edgeContributionReadout (B.virtualLocalization.edgeContribution e) := by
  rw [B.edgeContribution_eq_kB_log_edgeEulerWeight e]
  exact mul_nonneg B.laplacianCalibration.functional.kB_pos.le
    (Real.log_nonneg hweight)

end GWDrazinLaplacianBridge

end InfoGeometry.GromovWittenErlangen
