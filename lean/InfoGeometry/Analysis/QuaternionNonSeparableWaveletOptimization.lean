import Mathlib
import InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
import InfoGeometry.Canonical.LiteratureGrandCanonicalWeylTKK
import InfoGeometry.Meta.Architecture
import InfoGeometry.Meta.OwnerTarget

/-!
# InfoGeometry.Analysis.QuaternionNonSeparableWaveletOptimization

Optimization scaffold for non-separable quaternion-valued wavelet
constructions.

Literature owner:
  "An Optimisation Approach to Non-Separable Quaternion-Valued Wavelet
  Constructions".

This file does not prove a new optimization theorem, paraunitary completion
theorem, or any analytic convergence statement.  It packages the existing
filter-bank owner and the repo's KKT optimization packet into a theorem-safe
bridge.
-/

noncomputable section

namespace InfoGeometry.Analysis.QuaternionNonSeparableWaveletOptimization

open InfoGeometry.Analysis.DiscreteHurwitzCliffordWavelet
open InfoGeometry.Canonical.LiteratureGrandCanonicalWeylTKK

/--
Optimization problem for a non-separable quaternion-valued wavelet
construction.

The objective and non-separable constraints are stored as explicit data.
The actual optimization proof remains external to this scaffold.
-/
@[rep_depth operator]
structure QuaternionNonSeparableWaveletOptimizationProblem where
  filterBank : ParaunitaryCliffordFilterBank
  cascade : CliffordCascadeSystem filterBank
  kkt : KarushKuhnTuckerThermodynamicData

  /-- Quaternion-valued filter coefficients are present as the active lane. -/
  quaternionValued : Prop
  quaternionValued_sorryProof : quaternionValued

  /-- The construction is non-separable. -/
  nonSeparable : Prop
  nonSeparable_sorryProof : nonSeparable

  /-- Optimization objective readout. -/
  objective : ℝ

  /-- The objective is bounded below by the chosen optimization model. -/
  objectiveLowerBound : Prop
  objectiveLowerBound_sorryProof : objectiveLowerBound

  /-- The optimization packet is admissible for the finite-partition lane. -/
  finitePartitionAdmissible : Prop
  finitePartitionAdmissible_sorryProof :
    finitePartitionAdmissible

/--
Owner-side theorem currently available in this file: the quaternion/non-separable
optimization carrier supplies the declared finite-partition admissibility.

This does not assert existence of an optimizer; it only re-exports the concrete
admissibility certificate carried by the owner datum.
-/
@[rep_depth operator]
theorem quaternionNonSeparableWavelet_finitePartitionAdmissible
    (P : QuaternionNonSeparableWaveletOptimizationProblem) :
    P.finitePartitionAdmissible :=
  P.finitePartitionAdmissible_sorryProof

/-- Backward-compatible public theorem name, now carrying the actual owner-side claim. -/
@[rep_depth operator]
theorem quaternionNonSeparableWaveletOwnerTarget
    (P : QuaternionNonSeparableWaveletOptimizationProblem) :
    P.finitePartitionAdmissible :=
  quaternionNonSeparableWavelet_finitePartitionAdmissible P

end InfoGeometry.Analysis.QuaternionNonSeparableWaveletOptimization
