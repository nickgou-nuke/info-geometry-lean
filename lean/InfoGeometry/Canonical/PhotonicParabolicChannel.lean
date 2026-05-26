import InfoGeometry.Canonical.GeneralizedOperatorChiral
import InfoGeometry.Canonical.ParabolicContractionBridge

/-!
# InfoGeometry.Canonical.PhotonicParabolicChannel

Finite photonic channel readout on the parabolic (`Ω² = 0`) operator lane.

No global crystal-band theorem is claimed here; this is a local algebraic
contraction statement.
-/

namespace InfoGeometry.Canonical.PhotonicParabolicChannel

open InfoGeometry.Canonical.GeneralizedOperatorChiral.GeneralizedOperator

abbrev ParOp := InfoGeometry.Canonical.GeneralizedOperatorChiral.GeneralizedOperator 0

/-- Minimal channel labels for the local polarization readout. -/
inductive ChiralChannel
  | E_plus
  | E_minus
  | Parabolic
deriving DecidableEq, Repr

/--
Local channel classifier:
if `Ω² = 0`, classify as `Parabolic`; otherwise keep an `E_plus` placeholder.
-/
noncomputable def channelOfOmega (Ω : ParOp) : ChiralChannel :=
  by
    classical
    exact if mul Ω Ω = zero then ChiralChannel.Parabolic else ChiralChannel.E_plus

/-- Nilpotent collapse theorem: `Ω² = 0` forces the parabolic channel. -/
theorem chiral_collapse_to_parabolic
    (Ω : ParOp) (h_nilpotent : mul Ω Ω = zero) :
    channelOfOmega Ω = ChiralChannel.Parabolic := by
  unfold channelOfOmega
  simp [h_nilpotent]

/-- Concrete pure-directional witness from the parabolic contraction bridge. -/
theorem pure_directional_collapse (χ : ℝ) :
    channelOfOmega ({ scalar := (0 : ℝ), directional := χ } : ParOp) = ChiralChannel.Parabolic := by
  apply chiral_collapse_to_parabolic
  simpa using
    (InfoGeometry.Canonical.ParabolicContractionBridge.metricParabolic_kernel_witness χ)

end InfoGeometry.Canonical.PhotonicParabolicChannel
