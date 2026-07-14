import InfoGeometry.Canonical.FiniteFibonacciFourAnyonPaperBridge
import InfoGeometry.Canonical.HestenesPhaseSemilinear

/-!
# InfoGeometry.Canonical.FiniteFibonacciFourAnyonHestenesBridge

Finite Hestenes/Krein translation of the four-Fibonacci-anyon sector.

The paper speaks about complex analyticity of conformal blocks.  In this
repository, that language is translated into phase-axis preservation on the
real doubled carrier.  For the finite four-anyon surface, the relevant
theorem-level content is:

* the repo-native diagonal `b₁` / `b₃` readout preserves the channel label;
* the vacuum channel picks up the `q⁻⁴` phase;
* the Fibonacci channel picks up the `q³` phase;
* this is recorded as a Hestenes-style phase-axis preserving finite symmetry,
  not as complex-analytic conformal-block theory.

No conformal-block construction.
No hypergeometric continuation.
No complex analyticity theorem.
-/

namespace FiniteFibonacciFourAnyonHestenesBridge

open InfoGeometry.Canonical.FiniteFibonacciFourAnyonBlocks
open InfoGeometry.Canonical.FiniteFibonacciFourAnyonPaperBridge
open InfoGeometry.Canonical.HestenesPhaseSemilinear

/--
Finite Hestenes-style analyticity for the four-anyon phase readout:
the generator preserves the channel label.

This is the repo-native replacement for the paper's complex-analytic language
in the finite `n = 4` sector.
-/
def IsFourAnyonHestenesAnalytic
    (f : PhasedFourAnyonBlock → PhasedFourAnyonBlock) : Prop :=
  ∀ v : PhasedFourAnyonBlock, (f v).2 = v.2

/-- The repo-native diagonal four-anyon readout is Hestenes-analytic in the finite sense. -/
theorem diagonalRAction_isFourAnyonHestenesAnalytic (q : Units ℂ) :
    IsFourAnyonHestenesAnalytic (diagonalRAction q) := by
  intro v
  exact diagonalRAction_channel q v

/-- The vacuum basis vector is fixed at the channel level by the finite readout. -/
theorem fourAnyonVacuumBasis_channel (q : Units ℂ) :
    (diagonalRAction q fourAnyonVacuumBasis).2 = fourAnyonVacuumBasis.2 := by
  simp [fourAnyonVacuumBasis, diagonalRAction]

/-- The Fibonacci basis vector is fixed at the channel level by the finite readout. -/
theorem fourAnyonFibBasis_channel (q : Units ℂ) :
    (diagonalRAction q fourAnyonFibBasis).2 = fourAnyonFibBasis.2 := by
  simp [fourAnyonFibBasis, diagonalRAction]

/-- The repo-native finite Hestenes-style readout preserves the channel label. -/
theorem fourAnyonHestenesAnalytic (q : Units ℂ) :
    IsFourAnyonHestenesAnalytic (fun v => diagonalRAction q v) := by
  exact diagonalRAction_isFourAnyonHestenesAnalytic q

end FiniteFibonacciFourAnyonHestenesBridge
