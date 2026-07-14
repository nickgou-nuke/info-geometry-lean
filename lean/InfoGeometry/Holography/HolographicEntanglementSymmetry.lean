import InfoGeometry.Holography.RyuTakayanagiEmergence
import InfoGeometry.Canonical.HolographicEntanglementSymmetry

/-!
# Holographic Entanglement and Triality Symmetry

This file is the `Holography`-namespace interface for the owner theorem in
`InfoGeometry.Canonical.HolographicEntanglementSymmetry`.

It does not introduce density-matrix entropy, a Poincare minimal-surface
functional, a fresh triality group, or a local `E8`/`Spin(4,4)` constant.  The
current compiled owner surfaces are:

* the finite two-state entropy identity in `RyuTakayanagiEmergence`;
* the depth-indexed RT readout and finite triality-sector cycle in the canonical
  holographic bridge;
* the canonical real doubled Hestenes/Krein split-triality supercharge packet.
-/

set_option linter.unusedVariables false

noncomputable section

namespace HolographicEntanglementSymmetry

open InfoGeometry.Holography.RyuTakayanagiEmergence
open InfoGeometry.Canonical.TrialitySpin8Permutations
open InfoGeometry.Canonical.HolographicEntanglementSymmetry

/-! ### 1. Two-state entropy corridor -/

/-- The closed two-state entropy identity from the RT emergence owner. -/
theorem maxEntropy_is_ln2 :
    vonNeumannEntropy (1 / 2 : ℝ) = Real.log 2 :=
  maxEntropy_twoState

/-! ### 2. Ryu-Takayanagi finite bookkeeping -/

/-- Normalized finite Newton constant used by the two-state RT bookkeeping readout. -/
def newtonConstant : ℝ := 1 / 4

/-- At `G = 1/4`, the two-state entropy readout equals `Area / 4G`. -/
theorem rt_formula_with_newton_constant :
    vonNeumannEntropy (1 / 2 : ℝ) = Real.log 2 / (4 * newtonConstant) := by
  dsimp [newtonConstant]
  rw [maxEntropy_twoState]
  ring

/-- Ryu-Takayanagi bookkeeping relation for finite entropy and area data. -/
structure IsRyuTakayanagiMatch (stateEntropy bulkArea G : ℝ) : Prop where
  entropy_eq_area : stateEntropy = bulkArea / (4 * G)

/-- The normalized two-state datum satisfies the finite RT bookkeeping relation. -/
theorem maxent_is_rt_match :
    IsRyuTakayanagiMatch (Real.log 2) (Real.log 2) newtonConstant := by
  refine ⟨?entropy_eq_area⟩
  dsimp [newtonConstant]
  ring

/-! ### 3. Canonical triality owner access -/

/-- The canonical triality sector cycle closes after three applications. -/
theorem triality_order_three (s : TrialitySector) :
    (trialityCycle ^ 3) s = s :=
  trialityCycle_cube_apply s

/--
Holography-facing access to the canonical real doubled Hestenes/Krein packet.

The proof owner remains
`InfoGeometry.Canonical.HolographicEntanglementSymmetry`; this theorem only
exposes the packet from the `Holography` namespace.
-/
theorem canonical_hestenesKrein_triality_packet
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (s : TrialitySector) (n N : ℕ) :
    HolographicEntanglementTrialityPacket E s n N :=
  canonical_holographic_entanglement_triality_packet (E := E) s n N

/-! ### 4. Wrapper capstone -/

/--
Holography-facing capstone tying the two-state entropy readout to the canonical
depth-indexed RT/triality/Krein packet.
-/
theorem holographic_triality_capstone
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (s : TrialitySector) (n N : ℕ) :
    (vonNeumannEntropy (1 / 2 : ℝ) = Real.log 2) ∧
      ((trialityCycle ^ 3) s = s) ∧
      (vonNeumannEntropy (1 / 2 : ℝ) = Real.log 2 / (4 * newtonConstant)) ∧
      HolographicEntanglementTrialityPacket E s n N ∧
      braidEntanglementStep > 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact maxEntropy_twoState
  · exact triality_order_three s
  · exact rt_formula_with_newton_constant
  · exact canonical_hestenesKrein_triality_packet (E := E) s n N
  · exact braidEntanglementStep_pos

end HolographicEntanglementSymmetry
