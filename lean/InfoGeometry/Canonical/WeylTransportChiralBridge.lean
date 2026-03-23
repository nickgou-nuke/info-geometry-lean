import InfoGeometry.Canonical.WeylTransport
import InfoGeometry.Canonical.ConformalUnification

namespace InfoGeometry.Canonical.WeylTransportBridge

open InfoGeometry.Canonical.ConformalUnification

variable {I X A E : Type*}
variable [Fintype I]
variable [AddCommGroup A] [Module ℝ A]
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [FiniteDimensional ℝ E]

/--
Bridge datum from flat local Weyl transport to global chiral scale.

This packages the two semantic bridge steps:
1. flat local curvature implies zero integrated curvature,
2. zero integrated curvature implies global scalar chiral source.
-/
structure FlatCurvatureChiralScaleBridge
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X) where
  lineIntegrator : WeylLineIntegrator I A A
  holonomyMap : WeylHolonomyMap A ℝ
  flat_to_zeroCurvatureIntegral :
    ∀ B : WeylGaugeField X A,
      WeylGaugeField.IsFlat (Δ := Δ) B →
      lineIntegrator.integrateCurvature Δ B γ = 0
  zeroCurvatureIntegral_to_chiralScale :
    ∀ B : WeylGaugeField X A,
      lineIntegrator.integrateCurvature Δ B γ = 0 →
      lineIntegrator.holonomy holonomyMap B γ = CI.chiralScale

omit [Fintype I] [FiniteDimensional ℝ E] in
/--
Flat-curvature bridge theorem:
local Weyl flatness collapses transport to the global scalar chiral source.
-/
theorem holonomy_eq_chiralScale_of_flat
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge : FlatCurvatureChiralScaleBridge (CI := CI) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ = CI.chiralScale := by
  apply bridge.zeroCurvatureIntegral_to_chiralScale B
  exact bridge.flat_to_zeroCurvatureIntegral B hFlat

/--
Canonical finite-trajectory bridge constructor.

The flat-to-zero part is discharged by the concrete finite-sum integrator,
while the user supplies only the semantic reduction from zero curvature integral
into `CI.chiralScale`.
-/
def finiteSumFlatCurvatureChiralScaleBridge
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (H : WeylHolonomyMap A ℝ)
    (hZeroToChiral :
      ∀ B : WeylGaugeField X A,
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).integrateCurvature Δ B γ = 0 →
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).holonomy H B γ = CI.chiralScale) :
    FlatCurvatureChiralScaleBridge (CI := CI) (Δ := Δ) (γ := γ) where
  lineIntegrator := WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)
  holonomyMap := H
  flat_to_zeroCurvatureIntegral := by
    intro B hFlat
    exact WeylLineIntegrator.finiteSumIntegrator_integrateCurvature_eq_zero_of_flat
      (Δ := Δ) (B := B) (γ := γ) hFlat
  zeroCurvatureIntegral_to_chiralScale := by
    intro B hZero
    exact hZeroToChiral B hZero

omit [FiniteDimensional ℝ E] in
/--
Finite-trajectory flat-curvature theorem specialized to the canonical bridge.
-/
theorem finiteSum_holonomy_eq_chiralScale_of_flat
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (H : WeylHolonomyMap A ℝ)
    (B : WeylGaugeField X A)
    (hZeroToChiral :
      ∀ B' : WeylGaugeField X A,
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).integrateCurvature Δ B' γ = 0 →
        (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).holonomy H B' γ = CI.chiralScale)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B) :
    (WeylLineIntegrator.finiteSumIntegrator (I := I) (A := A)).holonomy H B γ = CI.chiralScale := by
  let bridge := finiteSumFlatCurvatureChiralScaleBridge
    (CI := CI) (Δ := Δ) (γ := γ) (H := H) hZeroToChiral
  simpa [bridge] using
    holonomy_eq_chiralScale_of_flat
      (CI := CI) (Δ := Δ) (γ := γ)
      (bridge := bridge)
      (B := B)
      hFlat


omit [Fintype I] in
/--
Flat Weyl holonomy collapses to zero when unit relative volume forces the
conformal inference into the normal phase.
-/
theorem holonomy_eq_zero_of_flat_of_unitRelativeVolume
    {n : Nat}
    (CI : ConformalInference E)
    (Δ : WeylDifferentialOperator ℝ X A)
    (γ : WeylTrajectory I X)
    (bridge : FlatCurvatureChiralScaleBridge (CI := CI) (Δ := Δ) (γ := γ))
    (B : WeylGaugeField X A)
    (hFlat : WeylGaugeField.IsFlat (Δ := Δ) B)
    (M : InfoGeometry.Canonical.MoE.SinkhornMatrix n)
    (hScaleFromKahler : CI.chiralScale = InfoGeometry.Canonical.MoE.kahlerPotentialRN n M)
    (hUnitVolume : InfoGeometry.Canonical.MoE.relativeVolumeChangeRN n M = 1) :
    bridge.lineIntegrator.holonomy bridge.holonomyMap B γ = 0 := by
  have hScaleZero :=
    CI.chiralScale_eq_zero_of_kahlerLogDet_unitRelativeVolume
      (M := M) hScaleFromKahler hUnitVolume
  rw [holonomy_eq_chiralScale_of_flat
      (CI := CI) (Δ := Δ) (γ := γ) (bridge := bridge) (B := B) hFlat]
  exact hScaleZero

end InfoGeometry.Canonical.WeylTransportBridge
