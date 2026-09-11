import Mathlib.Analysis.SpecialFunctions.Log.Basic
import InfoGeometry.Algebra.FiniteSpinAlgebra
import Mathlib.Algebra.BigOperators.Ring.Finset
import InfoGeometry.Canonical.FormalPrimeRootSystem
import InfoGeometry.Canonical.SouriauThermalEvaluation
import InfoGeometry.Canonical.PrimeGasPartitions
import InfoGeometry.Algebraic.SplitSuperGeometry

/-!
# InfoGeometry.Arithmetic.PrimeVielbeinSupervolume

Finite prime-vielbein specialization.

No infinite products.
No analytic continuation.
No zeta regularization.

The finite prime cutoff gives a finite Weyl/prime state space.
The supertrace is the alternating finite sum.
The supervolume is the finite Weyl denominator product.
The negative-log potential is gated by a positivity witness.
-/

noncomputable section

namespace InfoGeometry.Arithmetic

open scoped BigOperators
open InfoGeometry.Canonical.FormalPrimeRootSystem
open InfoGeometry.Canonical.SouriauThermalEvaluation
open InfoGeometry.Canonical.PrimeGasPartitions

/-- Finite prime-vielbein supertrace readout. -/
def finitePrimeVielbeinSupertrace {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) : ℝ :=
  finiteEvaluatedAlternatingSum E

/-- Finite prime-vielbein supervolume readout. -/
def finitePrimeVielbeinSupervolume {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) : ℝ :=
  finiteEvaluatedDenominator E

/--
Finite prime-vielbein Weyl identity.

This is the finite algebraic specialization of the supertrace/supervolume
corridor.
-/
theorem finitePrimeVielbeinSupertrace_eq_supervolume
    {L : FormalPrimeRootLattice}
    (E : SouriauThermalEvaluation L) :
    finitePrimeVielbeinSupertrace E = finitePrimeVielbeinSupervolume E := by
  simp [finitePrimeVielbeinSupertrace, finitePrimeVielbeinSupervolume]
  exact (finite_euler_weyl_identity E).symm

/--
Finite prime-vielbein readout.

The supertrace is the alternating finite sum, the supervolume is the finite
Weyl denominator, and the witness stores the equality between them.
-/
structure PrimeVielbeinReadout (L : FormalPrimeRootLattice) where
  evaluation : SouriauThermalEvaluation L
  supertraceReadout : ℝ
  supervolumeReadout : ℝ
  supertrace_eq_supervolume : supertraceReadout = supervolumeReadout

namespace PrimeVielbeinReadout

variable {L : FormalPrimeRootLattice}

/-- Canonical finite prime-vielbein readout. -/
def canonical (E : SouriauThermalEvaluation L) : PrimeVielbeinReadout L where
  evaluation := E
  supertraceReadout := finitePrimeVielbeinSupertrace (E := E)
  supervolumeReadout := finitePrimeVielbeinSupervolume (E := E)
  supertrace_eq_supervolume := finitePrimeVielbeinSupertrace_eq_supervolume E

end PrimeVielbeinReadout

/--
Positivity witness for a finite supervolume potential.

This keeps the negative logarithm explicit and proof-carrying.
-/
structure PrimeVielbeinGate (L : FormalPrimeRootLattice) where
  readout : PrimeVielbeinReadout L
  supervolume_pos : 0 < readout.supervolumeReadout

/--
Finite prime-vielbein effective action.

This is the finite negative log-supervolume potential.
-/
def finitePrimeVielbeinEffectiveAction
    {L : FormalPrimeRootLattice}
    (G : PrimeVielbeinGate L) : ℝ :=
  - Real.log G.readout.supervolumeReadout

@[simp]
theorem finitePrimeVielbeinEffectiveAction_eq_neg_log_supervolume
    {L : FormalPrimeRootLattice}
    (G : PrimeVielbeinGate L) :
    finitePrimeVielbeinEffectiveAction G =
      - Real.log G.readout.supervolumeReadout :=
  rfl

end InfoGeometry.Arithmetic
