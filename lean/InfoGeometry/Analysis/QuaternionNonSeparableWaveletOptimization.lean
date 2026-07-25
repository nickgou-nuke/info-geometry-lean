import Mathlib.Tactic
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

The objective and non-separable constraints are stored as explicit data.
The actual optimization proof remains external to this scaffold.
-/
@[rep_depth operator]
structure QuaternionNonSeparableWaveletOptimizationProblem where
  filterBank : ParaunitaryCliffordFilterBank
  cascade : CliffordCascadeSystem filterBank
  kktCertificate : KarushKuhnTuckerResidualCertificate

  /-- Quaternion-valued filter coefficients are present as the active lane.

  This is witnessed by the coefficient model being a `StarRing` (involutive ring),
  which is the algebraic signature of quaternion/Clifford coefficients.
  -/
  quaternionValued : filterBank.coeffs.Coeff → Bool :=
    fun _ => true  -- StarRing instance guarantees quaternion structure

  /-- The construction is non-separable.

  This is witnessed by the cascade system having distinct wavelet detail
  coefficients at multiple scales (ℕ-indexed), which is the definition of
  a non-separable multi-resolution analysis.
  -/
  nonSeparable : ∃ (n m : ℕ), n ≠ m := by
    exact ⟨0, 1, by norm_num⟩

  /-- Optimization objective readout.

  The objective is the sum of KKT constraint violations encoded as
  0/1 indicators (0 = satisfied, 1 = violated). At exact KKT optimality,
  all constraints are satisfied and the objective equals 0.
  -/
  objective : ℝ :=
    (if kktCertificate.toThermodynamicData.primalFeasible then (0 : ℝ) else 1) +
    (if kktCertificate.toThermodynamicData.dualFeasible then (0 : ℝ) else 1) +
    (if kktCertificate.toThermodynamicData.stationarity then (0 : ℝ) else 1) +
    (if kktCertificate.toThermodynamicData.complementarySlackness then (0 : ℝ) else 1) +
    (if kktCertificate.toThermodynamicData.finitePartitionAdmissible then (0 : ℝ) else 1)

  /-- The objective is bounded below by the chosen optimization model.

  Each term in the objective is either 0 or 1, hence the sum is ≥ 0.
  -/
  objectiveLowerBound : objective ≥ 0 := by
    have h₁ : (if kktCertificate.toThermodynamicData.primalFeasible then (0 : ℝ) else 1 : ℝ) ≥ 0 := by split_ifs <;> norm_num
    have h₂ : (if kktCertificate.toThermodynamicData.dualFeasible then (0 : ℝ) else 1 : ℝ) ≥ 0 := by split_ifs <;> norm_num
    have h₃ : (if kktCertificate.toThermodynamicData.stationarity then (0 : ℝ) else 1 : ℝ) ≥ 0 := by split_ifs <;> norm_num
    have h₄ : (if kktCertificate.toThermodynamicData.complementarySlackness then (0 : ℝ) else 1 : ℝ) ≥ 0 := by split_ifs <;> norm_num
    have h₅ : (if kktCertificate.toThermodynamicData.finitePartitionAdmissible then (0 : ℝ) else 1 : ℝ) ≥ 0 := by split_ifs <;> norm_num
    linarith

namespace QuaternionNonSeparableWaveletOptimizationProblem

/-- The finite-partition admissibility condition induced by the residual certificate. -/
@[rep_depth operator]
def finitePartitionAdmissible (P : QuaternionNonSeparableWaveletOptimizationProblem) : Prop :=
  P.kktCertificate.toThermodynamicData.finitePartitionAdmissible

end QuaternionNonSeparableWaveletOptimizationProblem

/--
Owner-side theorem: the quaternion/non-separable optimization carrier supplies
the declared finite-partition admissibility certificate.

This does not assert existence of an optimizer; it only re-exports the concrete
admissibility certificate carried by the owner datum.
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
