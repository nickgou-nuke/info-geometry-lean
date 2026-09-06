import InfoGeometry.Canonical.BipolarCartanLorentzBridge
import InfoGeometry.Canonical.DiscreteModularMellinShift
import InfoGeometry.Canonical.RealDoubledCliffordFiniteSpine
import InfoGeometry.Core.MajoranaLiftPacket

/-!
# Bipolar phase on the real doubled Hestenes--Krein carrier

The bipolar logarithm is complex-valued, while the repository's canonical
Hestenes--Krein carrier is real and doubled.  This file is only the adapter
between those two existing owners: the imaginary coordinate is read out by
the already defined real operator `doubledRealComplexScalar`.

No complex structure is added to the real carrier and no physical
interpretation is used.
-/

noncomputable section

namespace InfoGeometry.Canonical.BipolarRealDoubledKreinBridge

open InfoGeometry.Analysis.BipolarCrossRatioLog
open InfoGeometry.Canonical.BipolarCartanLorentzBridge
open InfoGeometry.Canonical.DiscreteModularMellinShift
open InfoGeometry.Krein

variable {E : Type 0}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

local notation "H₂" => DoubledSpace E
local notation "EndH" => H₂ →L[ℝ] H₂

def bipolarPhaseOperator (s : ℂ) : EndH :=
  doubledRealPhaseOperator (E := E) (theta s)

/- The phase adapter is exactly the existing Majorana/Hestenes scalar
   combination on the doubled real carrier. -/
theorem bipolarPhaseOperator_eq_majorana_scalar (s : ℂ) :
    bipolarPhaseOperator (E := E) s =
      doubledRealComplexScalar (E := E) (Real.cos (theta s))
        (Real.sin (theta s)) := by
  rfl

/- The phase adapter's unit axis is the same operator owned by the finite
   real doubled Clifford spine.  This is an equality of carriers, not a new
   Clifford representation. -/
theorem bipolarPhase_axis_eq_realCliffordK :
    doubledRealComplexScalar (E := E) 0 1 =
      InfoGeometry.Canonical.RealDoubledCliffordFiniteSpine.K (E := E) := by
  calc
    doubledRealComplexScalar (E := E) 0 1 = clockAxis (E := E) := by
      exact doubledRealComplexScalar_zero_one_eq_clockAxis (E := E)
    _ = InfoGeometry.Canonical.RealDoubledCliffordFiniteSpine.K (E := E) := by
      rfl

theorem bipolarPhase_axis_eq_canonicalMajoranaK :
    doubledRealComplexScalar (E := E) 0 1 =
      InfoGeometry.Core.canonicalMajoranaK (E := E) := by
  calc
    doubledRealComplexScalar (E := E) 0 1 = clockAxis (E := E) := by
      exact doubledRealComplexScalar_zero_one_eq_clockAxis (E := E)
    _ = InfoGeometry.Core.canonicalMajoranaK (E := E) := by
      rfl

@[simp] theorem bipolarPhaseOperator_zero (s : ℂ) (hθ : theta s = 0) :
    bipolarPhaseOperator (E := E) s = ContinuousLinearMap.id ℝ H₂ := by
  rw [bipolarPhaseOperator, hθ]
  exact doubledRealPhaseOperator_zero (E := E)

theorem doubledRealComplexScalar_mul
    (a b c d : ℝ) :
    doubledRealComplexScalar (E := E) a b *
        doubledRealComplexScalar (E := E) c d =
      doubledRealComplexScalar (E := E) (a * c - b * d) (a * d + b * c) := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [doubledRealComplexScalar, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.mul_apply, ContinuousLinearMap.id_apply, add_mul,
    mul_add, smul_eq_mul, map_smul]
  have hK := congrArg (fun T : EndH => T u) (clockAxis_sq (E := E))
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.id_apply] at hK
  rw [hK]
  module

theorem doubledRealPhaseOperator_add (θ φ : ℝ) :
    doubledRealPhaseOperator (E := E) (θ + φ) =
      doubledRealPhaseOperator (E := E) θ *
        doubledRealPhaseOperator (E := E) φ := by
  change doubledRealComplexScalar (E := E) (Real.cos (θ + φ))
      (Real.sin (θ + φ)) =
    doubledRealComplexScalar (E := E) (Real.cos θ) (Real.sin θ) *
      doubledRealComplexScalar (E := E) (Real.cos φ) (Real.sin φ)
  rw [doubledRealComplexScalar_mul]
  congr 1
  · rw [Real.cos_add]
  · rw [Real.sin_add]
    ring

theorem bipolarPhaseOperator_add (θ φ : ℝ) :
    doubledRealPhaseOperator (E := E) (θ + φ) =
      doubledRealPhaseOperator (E := E) θ *
        doubledRealPhaseOperator (E := E) φ :=
  doubledRealPhaseOperator_add (E := E) θ φ

theorem bipolarCriticalPhaseOperator (y : ℝ) :
    bipolarPhaseOperator (E := E) (criticalLine y) =
      doubledRealPhaseOperator (E := E) (theta (criticalLine y)) := rfl

end InfoGeometry.Canonical.BipolarRealDoubledKreinBridge
