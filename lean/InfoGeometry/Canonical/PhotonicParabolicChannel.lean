import InfoGeometry.Canonical.GeneralizedOperatorChiral
import InfoGeometry.Canonical.ParabolicContractionBridge

/-!
# InfoGeometry.Canonical.PhotonicParabolicChannel

Finite photonic channel readout on the parabolic (`Ω² = 0`) operator lane.

No global crystal-band theorem is claimed here; this is a local algebraic
contraction statement.
-/

namespace InfoGeometry.Canonical.PhotonicParabolicChannel

open GeneralizedOperatorChiral
open GeneralizedOperator

abbrev ParOp := GeneralizedOperator 0

/-- Minimal channel labels for the local polarization readout. -/
inductive ChiralChannel
  | E_plus
  | E_minus
  | Parabolic
  | NonParabolic
deriving DecidableEq, Repr

/--
Local channel classifier:
if `Ω² = 0`, classify as `Parabolic`; otherwise retain only the honest
non-parabolic classification.  A plus/elliptic refinement requires a separate
owner theorem and is not inferred here.
-/
noncomputable def channelOfOmega (Ω : ParOp) : ChiralChannel :=
  by
    classical
    exact if mul Ω Ω = zero then ChiralChannel.Parabolic else ChiralChannel.NonParabolic

/-- Nilpotent collapse theorem: `Ω² = 0` forces the parabolic channel. -/
theorem chiral_collapse_to_parabolic
    (Ω : ParOp) (h_nilpotent : mul Ω Ω = zero) :
    channelOfOmega Ω = ChiralChannel.Parabolic := by
  unfold channelOfOmega
  simp [h_nilpotent]

/-- Reverse direction: parabolic channel classification forces `Ω² = 0`. -/
theorem nilpotent_of_chiral_collapse
    (Ω : ParOp) (hPar : channelOfOmega Ω = ChiralChannel.Parabolic) :
    mul Ω Ω = zero := by
  unfold channelOfOmega at hPar
  by_cases h : mul Ω Ω = zero
  · exact h
  · simp [h] at hPar

/-- Exact classifier equivalence. -/
theorem chiral_collapse_iff_nilpotent (Ω : ParOp) :
    channelOfOmega Ω = ChiralChannel.Parabolic ↔ mul Ω Ω = zero := by
  constructor
  · exact nilpotent_of_chiral_collapse Ω
  · exact chiral_collapse_to_parabolic Ω

/-- Concrete pure-directional nilpotence theorem from the parabolic contraction bridge. -/
theorem pure_directional_nilpotent (χ : ℝ) :
  mul ({ scalar := (0 : ℝ), directional := χ } : ParOp)
      ({ scalar := (0 : ℝ), directional := χ } : ParOp) = zero := by
  simpa using (
    ParabolicContractionBridge.metricParabolic_kernel_nilpotent χ)

/-- Concrete pure-directional channel collapse. -/
theorem pure_directional_collapse (χ : ℝ) :
  channelOfOmega ({ scalar := (0 : ℝ), directional := χ } : ParOp) =
    ChiralChannel.Parabolic := by
  apply chiral_collapse_to_parabolic
  exact pure_directional_nilpotent χ

end InfoGeometry.Canonical.PhotonicParabolicChannel
