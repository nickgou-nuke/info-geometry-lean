import Mathlib.Tactic
import Mathlib.Algebra.Quaternion
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
open Classical

/--
Optimization problem for a non-separable quaternion-valued wavelet
construction.

The actual quaternionic and non-separability conditions are defined below as
typed mathematical predicates.  The optimization objective is derived from
the KKT residual property.
-/
@[rep_depth operator]
structure QuaternionNonSeparableWaveletOptimizationProblem where
  filterBank : ParaunitaryCliffordFilterBank
  cascade : CliffordCascadeSystem filterBank
  kktCertificate : KarushKuhnTuckerResidualCertificate

namespace QuaternionNonSeparableWaveletOptimizationProblem

/--
The coefficient carrier is genuinely quaternion-valued when it is ring
equivalent to Hamilton's real quaternion algebra.
-/
@[rep_depth operator]
def quaternionValued
    (P : QuaternionNonSeparableWaveletOptimizationProblem) : Prop :=
  Nonempty (P.filterBank.coeffs.Coeff ≃+* Quaternion ℝ)

/--
The cascade is non-separable when two actual wavelet-detail modes differ.
This replaces the unrelated arithmetic property that two scale indices differ.
-/
@[rep_depth operator]
def nonSeparable
    (P : QuaternionNonSeparableWaveletOptimizationProblem) : Prop :=
  ∃ n m : ℕ, P.cascade.waveletDetail n ≠ P.cascade.waveletDetail m

/--
Optimization objective: the sum of the five Boolean KKT residual indicators.
-/
@[rep_depth operator]
def objective
    (P : QuaternionNonSeparableWaveletOptimizationProblem) : ℝ :=
  (if P.kktCertificate.toThermodynamicData.primalFeasible then (0 : ℝ) else 1) +
  (if P.kktCertificate.toThermodynamicData.dualFeasible then (0 : ℝ) else 1) +
  (if P.kktCertificate.toThermodynamicData.stationarity then (0 : ℝ) else 1) +
  (if P.kktCertificate.toThermodynamicData.complementarySlackness then (0 : ℝ) else 1) +
  (if P.kktCertificate.toThermodynamicData.finitePartitionAdmissible then (0 : ℝ) else 1)

/-- The residual objective is nonnegative because every indicator is `0` or `1`. -/
@[rep_depth operator]
theorem objectiveLowerBound
    (P : QuaternionNonSeparableWaveletOptimizationProblem) :
    0 ≤ P.objective := by
  unfold objective
  split_ifs <;> norm_num

/-- The finite-partition admissibility condition induced by the residual property. -/
@[rep_depth operator]
def finitePartitionAdmissible (P : QuaternionNonSeparableWaveletOptimizationProblem) : Prop :=
  P.kktCertificate.toThermodynamicData.finitePartitionAdmissible

end QuaternionNonSeparableWaveletOptimizationProblem

/--
Owner-side theorem: the quaternion/non-separable optimization carrier supplies
the declared finite-partition admissibility property.

This does not assert existence of an optimizer; it only re-exports the concrete
admissibility property carried by the owner datum.
-/
@[rep_depth operator]
theorem quaternionNonSeparableWavelet_finitePartitionAdmissible
    (P : QuaternionNonSeparableWaveletOptimizationProblem) :
    P.finitePartitionAdmissible := by
  change P.kktCertificate.toThermodynamicData.finitePartitionAdmissible
  exact P.kktCertificate.finitePartitionAdmissible

/-- Backward-compatible public theorem name, now carrying the actual owner-side claim. -/
@[rep_depth operator]
theorem quaternionNonSeparableWaveletOwnerTarget
    (P : QuaternionNonSeparableWaveletOptimizationProblem) :
    P.finitePartitionAdmissible :=
  quaternionNonSeparableWavelet_finitePartitionAdmissible P

end InfoGeometry.Analysis.QuaternionNonSeparableWaveletOptimization
